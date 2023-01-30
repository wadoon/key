package de.uka.ilkd.key.proof.mgt.deps;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.MayUseMethodContractCondition;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;


/**
 * Stores the contract dependencies for all contracts in Java files.
 * A dependency from c1 to c2 exists iff a proof for contract c1 uses contract c2 (via the use contract rule).
 * To ensure that the dependency data is persistent, they are stored in dependency files and read on loading.
 */
public class ContractDependencyRepository {
    /**
     * The file name used for the dependency files of loaded folders
     */
    public static final String DEPENDENCY_FILE_NAME = ".key-deps";
    /**
     * The registered services
     */
    private final Services services;
    /**
     * A map of the loaded folders to all relevant Java files in that folder
     */
    private final Map<String, Set<String>> folderToFiles = new HashMap<>();
    /**
     * A map of loaded Java files to all methods in that file that have a specification
     */
    private final Map<String, Set<IProgramMethod>> fileToMethods = new HashMap<>();
    /**
     * A map of all loaded methods in Java files with specification to the contracts of that method
     */
    private final Map<IProgramMethod, Set<Contract>> methodToContracts = new HashMap<>();
    /**
     * All contracts for which dependencies have been registered
     */
    private final Set<Contract> contracts = new HashSet<>();
    /**
     * A map of dependencies for each contract
     */
    private final Map<Contract, ImmutableSet<Contract>> deps = new HashMap<>();
    /**
     * All relevant folders for which dependency files have been loaded or created
     */
    private Set<Path> folders;
    /**
     * Parser for dependency files
     */
    private DepFileParser parser;
    /**
     * A map of dependency arcs to the rule justifications that added this arc (even redundant additions)
     */
    private final Map<Pair<Contract, Contract>, List<RuleJustification>> modifyingRuleJustifications = new HashMap<>();
    /**
     * A map of dependency arcs to the rule applications that added this arc (even redundant additions). For contract axioms
     */
    private final Map<Pair<Contract, Contract>, List<RuleApp>> modifyingRuleApplications = new HashMap<>();


    public ContractDependencyRepository(Services s) {
        services = s;
    }

    /**
     * Initializes the dependency repository, i.e.:
     * - Find all contracts for methods and register the contracts, methods, files, and folders
     * - Attempt to read dependency files or create them
     * - Initialize the repository with any loaded information
     * - Add hook to save the information on program shutdown
     */
    public void initializeRepo() {
        // Find all contracts for which we must track deps
        for (Contract c : services.getSpecificationRepository().getAllContracts()) {
            // Only consider operational contracts
            if (c instanceof FunctionalOperationContract) {
                FunctionalOperationContract foc = (FunctionalOperationContract) c;
                IProgramMethod target = foc.getTarget();
                PositionInfo pi = target.getPositionInfo();
                URI uri = pi.getURI();
                // We only track files by the user, not jars (as there can be no cycle between jar and file)
                if (!uri.getScheme().equals("file")) {
                    continue;
                }
                String path = uri.getPath();
                add(path, target, c);
            }
        }

        // Find all relevant folders; each one has/will have a dep file
        folders = new HashSet<>();
        for (String filePath : fileToMethods.keySet()) {
            File f = new File(filePath);
            Path folder = f.toPath().getParent();
            folders.add(folder);
            String folderS = folder.toString();
            if (!folderToFiles.containsKey(folderS)) {
                folderToFiles.put(folderS, new HashSet<>());
            }
            folderToFiles.get(folderS).add(filePath);
        }
        // Store information from the files if available
        try {
            for (Path folder : folders) {
                // Attempt to read dep file or create an empty one
                DependencyInformation di = readOrCreateDepFile(folder);
                // Store the loaded info
                for (Map.Entry<String, FileDependencyInformation> e : di.getFileInformationEntries()) {
                    for (Map.Entry<Contract, Set<Contract>> d : e.getValue().getContractDependencies()) {
                        for (Contract toAdd : d.getValue()) {
                            addDependencyFromFile(d.getKey(), toAdd);
                        }
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            try {
                writeToFiles();
            } catch (IOException e) {
                // this is called at program exit, so we only print a console message
                e.printStackTrace();
            }
        }));
    }

    /**
     * Called when a new proof for a contract is started. Deletes all dependencies of that contract.
     * Deleting all dependencies is fine even when a proof rather than a problem/Java file is loaded,
     * since proofs are replayed. All dependencies of the proof are then added and thereby re-checked.
     * @param p The started proof
     */
    public void registerProof(Proof p) {
        // get the contract which is being verified in our current proof
        final ContractPO po = services.getSpecificationRepository().getContractPOForProof(p);
        if (po == null) {
            return;
        }
        final Contract c = po.getContract();

        if (deps.containsKey(c)) {
            deps.put(c, DefaultImmutableSet.nil());
        }
    }

    /**
     * Get all dependencies for a contract
     * @param c The contract for which to query
     * @return All contracts on which c depends
     */
    public ImmutableSet<Contract> getDependencies(Contract c) {
        if (!deps.containsKey(c)) {
            return DefaultImmutableSet.nil();
        }
        return deps.get(c);
    }

    /**
     * Adds a dependency that was stored in a dep file
     * @param addTo The contract to which we add the dependency
     * @param toAdd The contract on which <code>addTo</code> depends
     */
    private void addDependencyFromFile(Contract addTo, Contract toAdd) {
        if (!deps.containsKey(addTo)) {
            throw new IllegalArgumentException("Contract " + addTo.getName() + " is not registered.");
        }
        deps.put(addTo, deps.get(addTo).add(toAdd));
    }

    /**
     * Adds a dependency introduced by a rule application
     * @param addTo The contract to which we add the dependency
     * @param toAdd The contract on which <code>addTo</code> depends
     * @param rj The rule justification that adds the dependency
     */
    private void addDependenciesFromRule(Contract addTo, ImmutableSet<Contract> toAdd, RuleJustification rj) {
        if (!deps.containsKey(addTo)) {
            throw new IllegalArgumentException("Contract " + addTo.getName() + " is not registered.");
        }
        for (Contract a : toAdd) {
            deps.put(addTo, deps.get(addTo).add(a));
            // We must track which rule applications introduce which dependencies because rules can be pruned
            Pair<Contract, Contract> p = new Pair<>(addTo, a);
            if (!modifyingRuleJustifications.containsKey(p)) {
                modifyingRuleJustifications.put(p, new LinkedList<>());
            }
            modifyingRuleJustifications.get(p).add(rj);
        }
    }

    /**
     * Adds a dependency introduced by a rule application of contract axiom
     * @param addTo The contract to which we add the dependency
     * @param toAdd The contract on which <code>addTo</code> depends
     * @param ra The rule application that adds the dependency
     */
    private void addDependenciesFromContractAxiom(Contract addTo, ImmutableSet<Contract> toAdd, RuleApp ra) {
        if (!deps.containsKey(addTo)) {
            throw new IllegalArgumentException("Contract " + addTo.getName() + " is not registered.");
        }
        for (Contract a : toAdd) {
            deps.put(addTo, deps.get(addTo).add(a));
            // We must track which rule applications introduce which dependencies because rules can be pruned
            Pair<Contract, Contract> p = new Pair<>(addTo, a);
            if (!modifyingRuleApplications.containsKey(p)) {
                modifyingRuleApplications.put(p, new LinkedList<>());
            }
            modifyingRuleApplications.get(p).add(ra);
        }
    }

    /**
     * Adds a dependency introduced by a rule application if necessary
     * @param removeFrom The contract from which we remove the dependency
     * @param toRemove The contract on which <code>removeFrom</code> depends
     * @param rj The justification that added the dependency
     */
    private void removeDependenciesFromRule(Contract removeFrom, ImmutableSet<Contract> toRemove, RuleJustification rj) {
        if (!deps.containsKey(removeFrom)) {
            throw new IllegalArgumentException("Contract " + removeFrom.getName() + " is not registered.");
        }
        for (Contract r : toRemove) {
            Pair<Contract, Contract> p = new Pair<>(removeFrom, r);
            if (modifyingRuleJustifications.containsKey(p)) {
                List<RuleJustification> justifications = modifyingRuleJustifications.get(p);
                if (justifications.size() == 1) {
                    // It was the only justification; we can remove the dependency
                    modifyingRuleJustifications.remove(p);
                    deps.put(removeFrom, deps.get(removeFrom).remove(r));
                } else {
                    // Don't remove the dependency, but remove the rule application
                    justifications.remove(rj);
                }
            }
        }
    }

    /**
     * Adds a dependency introduced by a rule application if necessary
     * @param removeFrom The contract from which we remove the dependency
     * @param toRemove The contract on which <code>removeFrom</code> depends
     * @param ra The application that added the dependency
     */
    private void removeDependenciesFromContractAxiom(Contract removeFrom, ImmutableSet<Contract> toRemove, RuleApp ra) {
        if (!deps.containsKey(removeFrom)) {
            throw new IllegalArgumentException("Contract " + removeFrom.getName() + " is not registered.");
        }
        for (Contract r : toRemove) {
            Pair<Contract, Contract> p = new Pair<>(removeFrom, r);
            if (modifyingRuleApplications.containsKey(p)) {
                List<RuleApp> apps = modifyingRuleApplications.get(p);
                if (apps.size() == 1) {
                    // It was the only application; we can remove the dependency
                    modifyingRuleApplications.remove(p);
                    deps.put(removeFrom, deps.get(removeFrom).remove(r));
                } else {
                    // Don't remove the dependency, but remove the rule application
                    apps.remove(ra);
                }
            }
        }
    }

    /**
     * Introduces a dependency caused by a rule if necessary
     * @param p The current proof
     * @param r The rule application
     * @param rj The justification of the rule just applied
     */
    public void ruleApplied(Proof p, RuleApp r, RuleJustification rj) {
        if (rj == null) {
            return;
        }
        final ContractPO po = services.getSpecificationRepository().getContractPOForProof(p);
        if (po == null) {
            return;
        }
        final Contract originalContract = po.getContract();
        if (!rj.isAxiomJustification()) {
            if (rj instanceof RuleJustificationBySpec) {
                Contract contract = ((RuleJustificationBySpec) rj).getSpec();
                ImmutableSet<Contract> atomicContracts = services.getSpecificationRepository().splitContract(contract);
                assert atomicContracts != null;
                atomicContracts = services.getSpecificationRepository().getInheritedContracts(atomicContracts);
                addDependenciesFromRule(originalContract, atomicContracts, rj);
            }
        } else {
            // May be model method contract axiom
            if (r instanceof PosTacletApp) {
                PosTacletApp ta = (PosTacletApp) r;
                if (ta.rule() instanceof RewriteTaclet) {
                    RewriteTaclet rt = (RewriteTaclet) ta.rule();
                    if (rt.displayName().startsWith("Contract_axiom")) {
                        ImmutableSet<Contract> atomicContracts = extractContractsFromTaclet(rt);
                        addDependenciesFromContractAxiom(originalContract, atomicContracts, ta);
                    }
                }
            }
        }
    }

    /**
     * Removes a dependency caused by a rule if necessary
     * @param p The current proof
     * @param rj The justification of the rule just applied
     */
    public void ruleUnApplied(Proof p, RuleApp r, RuleJustification rj) {
        if (rj == null) {
            return;
        }
        final ContractPO po = services.getSpecificationRepository().getContractPOForProof(p);
        if (po == null) {
            return;
        }
        final Contract originalContract = po.getContract();
        if (!rj.isAxiomJustification()) {
            if (rj instanceof RuleJustificationBySpec) {
                Contract contract = ((RuleJustificationBySpec) rj).getSpec();
                ImmutableSet<Contract> atomicContracts = services.getSpecificationRepository().splitContract(contract);
                assert atomicContracts != null;
                atomicContracts = services.getSpecificationRepository().getInheritedContracts(atomicContracts);
                removeDependenciesFromRule(originalContract, atomicContracts, rj);
            }
        } else {
            // May be model method contract axiom
            if (r instanceof PosTacletApp) {
                PosTacletApp ta = (PosTacletApp) r;
                if (ta.rule() instanceof RewriteTaclet) {
                    RewriteTaclet rt = (RewriteTaclet) ta.rule();
                    if (rt.displayName().startsWith("Contract_axiom")) {
                        ImmutableSet<Contract> atomicContracts = extractContractsFromTaclet(rt);
                        removeDependenciesFromContractAxiom(originalContract, atomicContracts, ta);
                    }
                }
            }
        }
    }

    private ImmutableSet<Contract> extractContractsFromTaclet(RewriteTaclet rt) {
        ImmutableList<VariableCondition> conds = rt.getVariableConditions();
        assert conds.size() == 1 : "unexpected conditions size";
        MayUseMethodContractCondition mayUse = (MayUseMethodContractCondition) conds.head();
        Contract c = services.getSpecificationRepository().getContractByName(mayUse.getParameter());
        ImmutableSet<Contract> atomicContracts = services.getSpecificationRepository().splitContract(c);
        assert atomicContracts != null;
        return services.getSpecificationRepository().getInheritedContracts(atomicContracts);
    }

    /**
     * Calculates the hash of a contract
     * @param c The contract
     * @return The hash of the specification only
     */
    public int getSpecificationHash(Contract c) {
        return c.getPlainText(services).hashCode();
    }

    /**
     * Calculates the hash of a contract's implementation
     * @param c The contract
     * @return The hash of the implementation only
     */
    public int getImplementationHash(Contract c) {
        if (c instanceof FunctionalOperationContract) {
            FunctionalOperationContract foc = (FunctionalOperationContract) c;
            StringWriter sw = new StringWriter();
            PrettyPrinter pp = new PrettyPrinter(sw);
            try {
                foc.getTarget().prettyPrint(pp);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
            String out = sw.toString();
            return out.hashCode();
        }
        return 0;
    }

    /**
     * @param c The contract
     * @return Whether the contract has an implementation
     */
    public boolean hasImplementation(Contract c) {
        if (c instanceof FunctionalOperationContract) {
            FunctionalOperationContract foc = (FunctionalOperationContract) c;
            return foc.getTarget() != null;
        }
        return false;
    }

    /**
     * Add a contract; update maps
     * @param path The path of the file of the method
     * @param met The method of the contract
     * @param c The contract
     */
    private void add(String path, IProgramMethod met, Contract c) {
        deps.put(c, DefaultImmutableSet.nil());
        addMethodToFile(path, met);
        addContractToMethod(met, c);
        contracts.add(c);
    }

    /**
     * Register a method for a file
     * @param path The path of the file of the method
     * @param met The method of the contract
     */
    private void addMethodToFile(String path, IProgramMethod met) {
        if (!fileToMethods.containsKey(path)) {
            fileToMethods.put(path, new HashSet<>());
        }
        fileToMethods.get(path).add(met);
    }

    /**
     * Register a contract for a method
     * @param met The method of the contract
     * @param c The contract
     */
    private void addContractToMethod(IProgramMethod met, Contract c) {
        if (!methodToContracts.containsKey(met)) {
            methodToContracts.put(met, new HashSet<>());
        }
        methodToContracts.get(met).add(c);
    }

    /**
     * Attempts to read the dependency file or creates a new one
     * @param folderPath The path to the folder for which we read the dependency file
     * @return The dependency information stored in the dependency file
     * @throws IOException if file reading fails
     */
    private DependencyInformation readOrCreateDepFile(Path folderPath) throws IOException {
        File depFile = folderPath.resolve(DEPENDENCY_FILE_NAME).toFile();
        boolean exists = depFile.exists() && !depFile.isDirectory();

        try {
            if (exists) {
                return read(depFile);
            }
        } catch (DepFileParserException e) {
            // TODO: Log error
        }
        return createNewDepFile(folderPath.toFile(), depFile);
    }

    /**
     * Create a new dependency file
     * @param folder The folder in which the file is created
     * @param depFile The new Dependency file
     * @return The new (empty) dependency information
     */
    private DependencyInformation createNewDepFile(File folder, File depFile) {
        List<String> files = getJavaFiles(folder);
        HashMap<String, FileDependencyInformation> fileInfos = new HashMap<>();
        for (String f : files) {
            File file = new File(f);
            FileDependencyInformation fdi =  new FileDependencyInformation(file.getName());
            fileInfos.put(f, fdi);
        }
        DependencyInformation di = new DependencyInformation(folder.getAbsolutePath(), fileInfos);
        try {
            depFile.createNewFile();
            DepFileSaver fs = new DepFileSaver(services, di, depFile);
            fs.save();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return di;
    }

    /**
     * @param folder The folder to query
     * @return All *.java files in the folder
     */
    private List<String> getJavaFiles(File folder) {
        assert folder.isDirectory();

        List<String> v = new ArrayList<>();
        String[] list = folder.list();
        // mu(2008-jan-28): if the directory is not readable for the current user
        // list is set to null, which results in a NullPointerException.
        if (list != null) {
            for (String s : list) {
                String fullName = folder.getPath() + File.separator + s;
                if (s.endsWith(".java")) {
                    v.add(fullName);
                }
            }
        }

        return v;
    }

    /**
     * Update the dependency files
     * @throws IOException if writing to any dependency file fails
     */
    private void writeToFiles() throws IOException {
        Map<String, Map<String, FileDependencyInformation>> folderInfos = new HashMap<>();
        for (Map.Entry<String, Set<String>> entry : folderToFiles.entrySet()) {
            Map<String, FileDependencyInformation> fileInfos = new HashMap<>();
            for (String file : entry.getValue()) {
                FileDependencyInformation fdi = new FileDependencyInformation(file);
                Set<Contract> contracts = fileToMethods.get(file).stream()
                        .flatMap(m -> methodToContracts.get(m).stream())
                        .collect(Collectors.toSet());
                for (Contract c : contracts) {
                    for (Contract dep : deps.get(c)) {
                        fdi.addDep(c, dep);
                    }
                }
                fileInfos.put(file, fdi);
            }
            folderInfos.put(entry.getKey(), fileInfos);
        }
        for (Path folder : folders) {
            Map<String, FileDependencyInformation> fileInfos = folderInfos.get(folder.toString());
            DependencyInformation di = new DependencyInformation(folder.toAbsolutePath().toString(), fileInfos);
            File depFile = folder.resolve(DEPENDENCY_FILE_NAME).toFile();
            DepFileSaver fs = new DepFileSaver(services, di, depFile);
            fs.save();
        }
    }

    /**
     * @return The dependency file parser for this repository
     */
    private DepFileParser getDepFileParser() {
        if (parser == null) {
            parser = new DepFileParser(services);
        }
        return parser;
    }

    /**
     * @param f Dependency file to read
     * @return The parsed result of the file
     * @throws IOException if reading file fails
     * @throws DepFileParserException if parsing fails
     */
    private DependencyInformation read(File f) throws IOException, DepFileParserException {
        Path path = f.toPath();
        String in = Files.readString(path);
        String folderName = path.getParent().toString();
        return getDepFileParser().parse(folderName, in);
    }
}
