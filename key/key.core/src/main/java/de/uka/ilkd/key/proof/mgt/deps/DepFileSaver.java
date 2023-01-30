package de.uka.ilkd.key.proof.mgt.deps;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import java.io.*;

/**
 * Saves dependency information to a dependency file
 */
public class DepFileSaver {
    private static final String FORMAT_VERSION = "0.0.1";
    private static final String PRELUDE = "# DO NOT CHANGE THIS FILE! CHANGES MAY RESULT IN UNSOUND PROOFS.";

    /**
     * The registered services
     */
    Services services;
    /**
     * The dependency information to write
     */
    DependencyInformation di;
    /**
     * Target file
     */
    File file;

    public DepFileSaver(Services s, DependencyInformation di, File file) {
        this.services = s;
        this.di = di;
        this.file = file;
    }

    public DepFileSaver(Services s, DependencyInformation di, String filename) {
        this(s, di, new File(filename));
    }

    /**
     * Write dependency information to file
     * @throws IOException if writing to file fails
     */
    public void save() throws IOException {
        save(new FileOutputStream(file));
    }

    /**
     * Write dependency information to output stream
     * @param out Target stream
     * @throws IOException if writing to stream fails
     */
    public void save(OutputStream out) throws IOException {
        try (var ps = new PrintWriter(out, true)) {
            ps.println(PRELUDE);
            ps.println("# Format version " + FORMAT_VERSION);
            ps.println("# Dep-file for folder '" + di.getFolderName() + "'");
            ps.println();
            writeDependencies(ps);
        }
    }

    /**
     * Write information to writer
     * @param ps print writer
     */
    private void writeDependencies(PrintWriter ps) {
        for (FileDependencyInformation fdi : di.getFileDependencyInfos()) {
            ps.println(fdi.getFilePath() + " {");
            for (Contract c : fdi.getContracts()) {
                ps.print('\t');
                writeContract(c, ps);
                ps.println(" {");
                for (Contract d : fdi.getDependencies(c)) {
                    ps.print("\t\t");
                    writeContract(d, ps);
                    ps.println();
                }
                ps.println("\t}");
            }
            ps.println("}");
            ps.println();
        }
    }

    /**
     * Write the contract information
     * @param c Contract
     * @param ps The writer to write to
     */
    private void writeContract(Contract c, PrintWriter ps) {
        ps.print(c.getName());
        ps.print('|');
        ps.print(services.getContractDependencyRepository().getSpecificationHash(c));
        if (c instanceof FunctionalOperationContract) {
            ps.print(services.getContractDependencyRepository().getImplementationHash(c));
        }
    }
}
