package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.AbstractServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.parser.ABSDefaultTermParser;
import de.uka.ilkd.key.parser.TermParser;
import de.uka.ilkd.key.pp.UIConfiguration;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.keyabs.init.ABSProfile;
import de.uka.ilkd.keyabs.proof.mgt.ABSSpecificationRepository;

public class ABSServices extends AbstractServices {

    private final ABSInfo info;

    /**
     * specification repository
     */
    private ABSSpecificationRepository specRepos = new ABSSpecificationRepository(this);
    
    public ABSServices(KeYExceptionHandler handler, KeYABSMapping program2key) {
        super(handler);
        setTypeConverter(new ABSTypeConverter(this));
        this.info = new ABSInfo(this, program2key);
    }
    
    public ABSServices (KeYExceptionHandler handler) {
        this(handler, new KeYABSMapping());
    }

    public ABSServices (KeYABSMapping map) {
        this(null, map);
    }

    public ABSServices () {
        this(null, new KeYABSMapping());
    }
    
    @Override
    public ABSTypeConverter getTypeConverter() {
        return (ABSTypeConverter) typeconverter;
    }

    @Override
    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder);
        nameRecorder = new NameRecorder();
    }

    @Override
    public void addNameProposal(Name proposal) {
        nameRecorder.addProposal(proposal);
    }

    @Override
    public ABSSpecificationRepository getSpecificationRepository() {
        return specRepos;
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
    public ABSServices copy() {
        ABSServices s = new ABSServices(getProgramInfo().rec2key().copy());
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setExceptionHandler(getExceptionHandler());
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    @Override
    public ABSServices copyProofSpecific(Proof p_proof) {
        ABSServices s = new ABSServices(getProgramInfo().rec2key());
        s.proof = proof;
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
    public TermBuilder getTermBuilder() {
        return TermBuilder.DF;
    }

    @Override
    public ABSInfo getProgramInfo() {
        return info;
    }

    @Override
    public TermParser getTermParser() {
        return new ABSDefaultTermParser();
    }

	@Override
	public UIConfiguration getUIConfiguration() {
		return ABSProfile.UNPARSER;
	}

}
