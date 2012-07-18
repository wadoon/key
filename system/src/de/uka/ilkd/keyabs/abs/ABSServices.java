package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.AbstractServices;
import de.uka.ilkd.key.java.IProgramInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public class ABSServices extends AbstractServices {

    public ABSServices(KeYExceptionHandler handler) {
        super(handler);
    }

    @Override
    public ABSTypeConverter getTypeConverter() {
        return null;
    }

    @Override
    public void saveNameRecorder(Node n) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addNameProposal(Name proposal) {
        // TODO Auto-generated method stub

    }

    @Override
    public SpecificationRepository getSpecificationRepository() {
        // TODO Auto-generated method stub
        return null;
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
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ABSServices copyProofSpecific(Proof p_proof) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IProgramInfo getJavaInfo() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public TermBuilder getTermBuilder() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ABSInfo getProgramInfo() {
        // TODO Auto-generated method stub
        return null;
    }

}
