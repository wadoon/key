package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.AbstractServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.parser.ABSDefaultTermParser;
import de.uka.ilkd.key.parser.TermParser;
import de.uka.ilkd.key.pp.UIConfiguration;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.keyabs.abs.converter.ABSModelParserInfo;
import de.uka.ilkd.keyabs.proof.init.ABSProfile;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.proof.mgt.ABSSpecificationRepository;

public class ABSServices extends AbstractServices {

    private final ABSInfo info;

    /**
     * specification repository
     */
    private ABSSpecificationRepository specRepos = 
            new ABSSpecificationRepository(this);

    public ABSServices() {
        this(null, new KeYABSMapping());
    }

    public ABSServices(KeYExceptionHandler handler) {
        this(handler, new KeYABSMapping());
    }


    private ABSServices(KeYABSMapping map, ABSInfo info) {
        this(null, map, info.getABSParserInfo());
    }

    private ABSServices(KeYExceptionHandler handler, KeYABSMapping program2key) {
        super(handler);
        setTypeConverter(new ABSTypeConverter(this));
        this.info = new ABSInfo(this, program2key);
    }

    private ABSServices(KeYExceptionHandler handler, KeYABSMapping program2key, ABSModelParserInfo parserInfo) {
        super(handler);
        setTypeConverter(new ABSTypeConverter(this));
        this.info = new ABSInfo(this, program2key, parserInfo);
    }

    @Override
    public void addNameProposal(Name proposal) {
        nameRecorder.addProposal(proposal);
    }

    @Override
    public ABSServices copy() {
        ABSServices s = new ABSServices(getProgramInfo().rec2key().copy(), info);
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setExceptionHandler(getExceptionHandler());
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    @Override
    public ABSServices copyPreservesLDTInformation() {
        ABSServices s = new ABSServices(getExceptionHandler());
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    @Override
    public ABSServices copyProofSpecific(Proof p_proof) {
        ABSServices s = new ABSServices(getProgramInfo().rec2key(), info);
        s.proof = p_proof;
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setExceptionHandler(getExceptionHandler());
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    @Override
    public ABSInfo getJavaInfo() {
        return info;
    }

    @Override
    public ABSInfo getProgramInfo() {
        return info;
    }

    @Override
    public ABSSpecificationRepository getSpecificationRepository() {
        return specRepos;
    }

    @Override
    public ABSTermBuilder getTermBuilder() {
        return ABSTermBuilder.TB;
    }

    @Override
    public TermParser getTermParser() {
        return new ABSDefaultTermParser();
    }

    @Override
    public ABSTypeConverter getTypeConverter() {
        return (ABSTypeConverter) typeconverter;
    }

    @Override
    public UIConfiguration getUIConfiguration() {
        return ABSProfile.UNPARSER;
    }

    @Override
    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder);
        nameRecorder = new NameRecorder();
    }

    public Function getIInvFor(KeYJavaType type) {
        return (Function) namespaces.functions().lookup(new Name(type.getFullName()+"$IInv"));
    }

    public Function getCInv() {
        return (Function) namespaces.functions().lookup(new Name("CInv"));
    }
}
