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
    private final DependencyClusterSpec origDependencyClusterSpec;
    
    final boolean hasRealModifiesClause;

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
            DependencyClusterSpec dependencyClusterSpec,
            boolean toBeSaved) {
        this(baseName, forClass, pm, specifiedIn, modality, pre, mby, mod, hasRealMod, self, params, result, exc, heapAtPre, dep, dependencyClusterSpec, toBeSaved, INVALID_ID);
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
                                        DependencyClusterSpec dependencyClusterSpec,
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
        this.origDependencyClusterSpec = dependencyClusterSpec;

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
        "<b>ID </b>" + origDependencyClusterSpec.getLabel() +"<br>" +
        "<b>LowIn </b>" + origDependencyClusterSpec.getLowIn() +"<br>" +
        "<b>LowOut </b>" + origDependencyClusterSpec.getLowOut() +"<br>" +
        "<b>LowState </b>" + origDependencyClusterSpec.getLowState() +"<br>" +
        "<b>Visible </b>" + origDependencyClusterSpec.getVisible() +"<br>" +
        "<b>New Objects </b>" + origDependencyClusterSpec.getNewObjects() +"<br>" +
        "</html>";
    }

    @Override
    public String getPlainText(Services services) {
        // TODO implement
        return "plain text for: "
                + origDependencyClusterSpec;
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
                origResult, origExc, origAtPre, origDep, origDependencyClusterSpec, toBeSaved, newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new DependencyClusterContractImpl(baseName, newKJT, (IProgramMethod)newPM, specifiedIn, modality, origPre, origMby, origMod, hasRealModifiesClause, origSelf, origParams, 
                origResult, origExc, origAtPre, origDep, origDependencyClusterSpec, toBeSaved, id);
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
    public DependencyClusterSpec getSpecs() {
        return origDependencyClusterSpec;
    }

    @Override
    public Term getSelf() {
        if (origSelf == null){
            assert pm.isStatic() : "missing self variable in non-static method contract";
            return null;
        }
        return origSelf;
    }

    @Override
    public String getLabel() {
        return getSpecs().getLabel();
    }
}
