package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.dependencycluster.po.DependencyClusterContractPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.util.DependencyClusterSpec;

public class DependencyClusterContractImpl
        implements DependencyClusterContract {

    //public static final Contract DUMMY_DEP_CLUSTER_CONTRACT = new DependencyClusterContractImpl();
    
    private final int id;
    private final KeYJavaType forClass;
    private final IProgramMethod pm;
    private final KeYJavaType specifiedIn;
    private final String baseName;
    private final String name;
    private final Term origPre;
    private final Term origMby;
    private final Term origMod;
    private final Modality modality;
    private final Term origSelf;
    private final ImmutableList<Term> origParams;
    private final Term origResult;
    private final Term origExc;
    private final Term origAtPre;
    private final boolean toBeSaved;
    private final Term origDep;
    private final ImmutableList<DependencyClusterSpec> origDependencyClusterSpecs;
    
    final boolean hasRealModifiesClause;
    
    /*
    private DependencyClusterContractImpl() {
        this.id = INVALID_ID;
        this.name = null;
        this.baseName = null;
        this.forClass = null;
        this.pm = null;
        this.specifiedIn = null;
        this.origPre = null;
        this.origMby = null;
        this.origMod = null;
        this.origSelf = null;
        this.origParams = null;
        this.origResult = null;
        this.origExc = null;
        this.origAtPre = null;
        this.modality = null;
        this.toBeSaved = false;
        this.origDep = null;
        this.origDependencyClusterSpecs = null;
        this.hasRealModifiesClause = false;
    }
    */
    public DependencyClusterContractImpl(String baseName,
            KeYJavaType forClass,
            IProgramMethod pm,
            KeYJavaType specifiedIn,
            Modality modality,
            Term pre,
            Term mby,
            Term mod,
            boolean hasRealMod,
            Term self,
            ImmutableList<Term> params,
            Term result,
            Term exc,
            Term heapAtPre,
            Term dep,
            ImmutableList<DependencyClusterSpec> dependencyClusterSpecs,
            boolean toBeSaved) {
        this(baseName, forClass, pm, specifiedIn, modality, pre, mby, mod, hasRealMod, self, params, result, exc, heapAtPre, dep, dependencyClusterSpecs, toBeSaved, INVALID_ID);
    }
    
    protected DependencyClusterContractImpl(String baseName,
                                        KeYJavaType forClass,
                                        IProgramMethod pm,
                                        KeYJavaType specifiedIn,
                                        Modality modality,
                                        Term pre,
                                        Term mby,
                                        Term mod,
                                        boolean hasRealMod,
                                        Term self,
                                        ImmutableList<Term> params,
                                        Term result,
                                        Term exc,
                                        Term heapAtPre,
                                        Term dep,
                                        ImmutableList<DependencyClusterSpec> dependencyClusterSpecs,
                                        boolean toBeSaved,
                                        int id) {
        this.id = id;
        this.baseName = baseName;
        this.name = ContractFactory.generateContractName(baseName, forClass, pm, specifiedIn, id);
        this.forClass = forClass;
        this.pm = pm;
        this.specifiedIn = specifiedIn;
        this.origPre = pre;
        this.origMby = mby;
        this.origMod = mod;
        this.origSelf = self;
        this.origParams = params;
        this.origResult = result;
        this.origExc = exc;
        this.origAtPre = heapAtPre;
        this.modality = modality;
        this.hasRealModifiesClause  = hasRealMod;
        this.toBeSaved = toBeSaved;
        this.origDep = dep;
        this.origDependencyClusterSpecs = dependencyClusterSpecs;
        /*
        System.out.println("id: " + this.id);
        System.out.println("baseName: " + this.baseName);
        System.out.println("name: " + this.name);
        System.out.println("forClass: " + this.forClass);
        System.out.println("pm: " + this.pm);
        System.out.println("specifiedIn: " + this.specifiedIn);
        System.out.println("origPre: " + this.origPre);
        System.out.println("origMby: " + this.origMby);
        System.out.println("origMod: " + this.origMod);
        System.out.println("origSelf: " + this.origSelf);
        System.out.println("origParams: " + this.origParams);
        System.out.println("origResult: " + this.origResult);
        System.out.println("origExc: " + this.origExc);
        System.out.println("origAtPre: " + this.origAtPre);
        System.out.println("modality: " + this.modality);
        System.out.println("hasRealModifiesClause: " + this.hasRealModifiesClause);
        System.out.println("toBeSaved: " + this.toBeSaved);
        System.out.println("origDep: " + this.origDep);
        System.out.println("origDependencyClusterSpecs: " + this.origDependencyClusterSpecs);
        */
    }

    @Override
    public int id() {
        return id;
    }

    @Override
    public IProgramMethod getTarget() {
        return pm;
    }

    @Override
    public boolean hasMby() {
        return origMby != null;
    }

    @Override
    public OriginalVariables getOrigVars() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms,
            Map<LocationVariable, Term> atPres, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getRequires(LocationVariable heap) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getAssignable(LocationVariable heap) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getAccessible(ProgramVariable heap) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getGlobalDefs() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getMby() {
        return origMby;
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getHTMLText(Services services) {
        // TODO implement
        return "<html>" +
        "<b>LowIn </b>" + origDependencyClusterSpecs.head().getLowIn() +"<br>" +
        "<b>LowOut </b>" + origDependencyClusterSpecs.head().getLowOut() +"<br>" +
        "<b>LowState </b>" + origDependencyClusterSpecs.head().getLowState() +"<br>" +
        "<b>Visible </b>" + origDependencyClusterSpecs.head().getVisible() +"<br>" +
        "<b>New Objects </b>" + origDependencyClusterSpecs.head().getNewObjects() +"<br>" +
        "</html>";
    }

    @Override
    public String getPlainText(Services services) {
        // TODO implement
        return "plain text for: "
                + origDependencyClusterSpecs;
    }

    @Override
    public boolean toBeSaved() {
        return toBeSaved;
    }

    @Override
    public boolean transactionApplicableContract() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public String proofToString(Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
        return new DependencyClusterContractPO(initConfig, this);
    }

    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
            Contract contract) {
        return new DependencyClusterContractPO(initConfig, (DependencyClusterContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
            Contract contract, boolean supportSymbolicExecutionAPI) {
        //TODO JK what does this do?
        throw new IllegalStateException("TODO JK why am I here?");
        //return createProofObl(initConfig, contract);

    }

    @Override
    public Contract setID(int newId) {
        return new DependencyClusterContractImpl(baseName, forClass, pm, specifiedIn, modality, origPre, origMby, origMod, hasRealModifiesClause, origSelf, origParams, 
                origResult, origExc, origAtPre, origDep, origDependencyClusterSpecs, toBeSaved, newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new DependencyClusterContractImpl(baseName, newKJT, (IProgramMethod)newPM, specifiedIn, modality, origPre, origMby, origMod, hasRealModifiesClause, origSelf, origParams, 
                origResult, origExc, origAtPre, origDep, origDependencyClusterSpecs, toBeSaved, id);
    }

    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, forClass, pm,
                specifiedIn);
    }

    @Override
    public boolean hasSelfVar() {
        return origSelf != null;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, forClass, pm,
                specifiedIn, id);
    }

    @Override
    public VisibilityModifier getVisibility() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return forClass;
    }

    @Override
    public Modality getModality() {
        return modality;
    }

    @Override
    public KeYJavaType getSpecifiedIn() {
        return specifiedIn;
    }

    @Override
    public Term getPre() {
        return origPre;
    }

    @Override
    public Term getMod() {
        return origMod;
    }

    @Override
    public boolean hasModifiesClause() {
        return hasRealModifiesClause;
    }

    @Override
    public Term getSelfVar() {
       
        return origSelf;
    }

    @Override
    public ImmutableList<Term> getParams() {
        
        return origParams;
    }

    @Override
    public Term getResult() {

        return origResult;
    }

    @Override
    public Term getExc() {
        
        return origExc;
    }

    @Override
    public Term getDep() {
        
        return origDep;
    }

    @Override
    public Term getHeapAtPre() {
       
        return origAtPre;
    }

    @Override
    public ImmutableList<DependencyClusterSpec> getSpecs() {
        return origDependencyClusterSpecs;
    }

}
