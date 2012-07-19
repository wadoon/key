// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;


import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.SchemaCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.TermParser;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

/**
 * this is a collection of common services to the KeY prover. Services
 * include information on the underlying Java model and a converter to
 * transform Java program elements to logic (where possible) and back.
 */
public class Services extends AbstractServices {

    /** used to determine whether an expression is a compile-time 
     * constant and if so the type and result of the expression
     */
    private ConstantExpressionEvaluator cee;

    /**
     * the information object on the Java model
     */
    private final JavaInfo javainfo;

    /**
     * specification repository
     */
    private SpecificationRepository specRepos = new SpecificationRepository(this);

    /**
     * creates a new Services object with a new TypeConverter and a new
     * JavaInfo object with no information stored at none of these.
     */
    public Services(KeYExceptionHandler exceptionHandler){
        super(exceptionHandler);
        setTypeConverter(new TypeConverter(this));
        cee = new ConstantExpressionEvaluator(this);
        javainfo = new JavaInfo
                (new KeYProgModelInfo(this, getTypeConverter(), this.exceptionHandler), this);
    }


    // ONLY for tests
    public Services() { 
        this((KeYExceptionHandler) null);
    }    

    
    private Services(KeYCrossReferenceServiceConfiguration crsc, 
            KeYRecoderMapping rec2key) {
        super(new KeYRecoderExcHandler());
        setTypeConverter(new TypeConverter(this));
        cee = new ConstantExpressionEvaluator(this);
        //	exceptionHandler = new KeYRecoderExcHandler();
        javainfo = new JavaInfo
                (new KeYProgModelInfo(this, crsc, rec2key, getTypeConverter()), this);
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#getTypeConverter()
     */
    @Override
    public TypeConverter getTypeConverter(){
        return (TypeConverter) typeconverter;
    }


    /**
     * Returns the ConstantExpressionEvaluator associated with this Services object.
     */
    public ConstantExpressionEvaluator getConstantExpressionEvaluator() {
        return cee;
    }


    /**
     * Returns the JavaInfo associated with this Services object.
     */
    public JavaInfo getJavaInfo() {
        return javainfo;
    }

    /**
     * Returns the JavaInfo associated with this Services object.
     */
    @Override
    public JavaInfo getProgramInfo() {
        return javainfo;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#saveNameRecorder(de.uka.ilkd.key.proof.Node)
     */
    @Override
    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder);
        nameRecorder = new NameRecorder();
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#addNameProposal(de.uka.ilkd.key.logic.Name)
     */
    @Override
    public void addNameProposal(Name proposal) {
        nameRecorder.addProposal(proposal);
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#getSpecificationRepository()
     */
    @Override
    public SpecificationRepository getSpecificationRepository() {
        return specRepos;
    }



    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#copy()
     */
    @Override
    public Services copy() {
        Debug.assertTrue
        (!(getJavaInfo().getKeYProgModelInfo().getServConf() 
                instanceof SchemaCrossReferenceServiceConfiguration),
                "services: tried to copy schema cross reference service config.");
        Services s = new Services
                (getJavaInfo().getKeYProgModelInfo().getServConf(),
                        getJavaInfo().getKeYProgModelInfo().rec2key().copy());
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setExceptionHandler(getExceptionHandler());
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#copyPreservesLDTInformation()
     */
    @Override
    public Services copyPreservesLDTInformation() {
        Debug.assertTrue
        (!(javainfo.getKeYProgModelInfo().getServConf() 
                instanceof SchemaCrossReferenceServiceConfiguration),
                "services: tried to copy schema cross reference service config.");
        Services s = new Services(getExceptionHandler());
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.IServices#copyProofSpecific(Proof)
     */
    @Override
    public Services copyProofSpecific(Proof p_proof) {
        final Services s = new Services(getJavaInfo().getKeYProgModelInfo().getServConf(),
                getJavaInfo().getKeYProgModelInfo().rec2key());
        s.proof = p_proof;
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setExceptionHandler(getExceptionHandler());
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }


    @Override
    public TermBuilder getTermBuilder() {
        return JavaProfile.DF();
    }


    @Override
    public TermParser getTermParser() {
        return new DefaultTermParser();
    }

}
