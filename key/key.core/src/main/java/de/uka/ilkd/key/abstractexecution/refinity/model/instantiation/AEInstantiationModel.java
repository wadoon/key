// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model.instantiation;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;
import javax.xml.bind.annotation.XmlType;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.java.Services;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(namespace = "http://www.key-project.org/abstractexecution")
@XmlType(propOrder = { "program", "methodLevelContext", "abstractLocationSets",
        "functionDeclarations", "predicateDeclarations", "programVariableDeclarations",
        "predicateInstantiations", "functionInstantiations" })
@XmlAccessorType(value = XmlAccessType.FIELD)
public class AEInstantiationModel {
    private static final String AE_INSTANTIATION_FILE_ENDING = ".aei";
    private static final String SCHEMA_PATH = "/de/uka/ilkd/key/refinity/aeiSchema1.xsd";

    @XmlElement(name = "program")
    private String program = "";

    // Currently unsupported
    @XmlElement(name = "methodLevelContext")
    private String methodLevelContext = "";

    @XmlAttribute(name = "preCondition")
    private String preCondition = "";

    @XmlAttribute(name = "postCondition")
    private String postCondition = "";

    @XmlElementWrapper(name = "predicates")
    @XmlElement(name = "predicate")
    private List<PredicateDeclaration> predicateDeclarations = new ArrayList<>();

    @XmlElementWrapper(name = "functions")
    @XmlElement(name = "function")
    private List<FunctionDeclaration> functionDeclarations = new ArrayList<>();

    @XmlElementWrapper(name = "locationSets")
    @XmlElement(name = "locationSet")
    private List<FunctionDeclaration> abstractLocationSets = new ArrayList<>();

    @XmlElementWrapper(name = "programVariables")
    @XmlElement(name = "programVariable")
    private List<ProgramVariableDeclaration> programVariableDeclarations = new ArrayList<>();

    @XmlElementWrapper(name = "predicateInstantiations")
    @XmlElement(name = "predicateInst")
    private List<PredicateInstantiation> predicateInstantiations = new ArrayList<>();

    @XmlElementWrapper(name = "functionInstantiations")
    @XmlElement(name = "functionInst")
    private List<FunctionInstantiation> functionInstantiations = new ArrayList<>();

    @XmlTransient
    private Optional<File> file = Optional.empty();

    public static AEInstantiationModel defaultModel() {
        final String postCondition = "\\result_1==\\result_2";
        final List<FunctionDeclaration> abstractLocationSets = Collections
                .singletonList(new FunctionDeclaration("relevant", "LocSet"));

        return new AEInstantiationModel("", "", postCondition, abstractLocationSets,
                Collections.emptyList(), Collections.emptyList(), Collections.emptyList(),
                Collections.emptyList(), Collections.emptyList());
    }

    public AEInstantiationModel(final String program, String methodLevelContext,
            final String postCondition, final List<FunctionDeclaration> abstractLocationSets,
            final List<FunctionDeclaration> functionDeclarations,
            final List<PredicateDeclaration> predicateDeclarations,
            final List<ProgramVariableDeclaration> programVariableDeclarations,
            final List<PredicateInstantiation> predicateInstantiations,
            final List<FunctionInstantiation> functionInstantiations) {
        this.program = program;
        this.methodLevelContext = methodLevelContext;
        this.postCondition = postCondition;
        this.abstractLocationSets = abstractLocationSets;
        this.functionDeclarations = functionDeclarations;
        this.predicateDeclarations = predicateDeclarations;
        this.programVariableDeclarations = programVariableDeclarations;

        this.predicateInstantiations = predicateInstantiations;
        this.functionInstantiations = functionInstantiations;
    }

    AEInstantiationModel() {
    }

    public String getProgram() {
        return program;
    }

    public String getPostCondition() {
        return postCondition;
    }

    public void setPostCondition(String postCondition) {
        this.postCondition = postCondition;
    }

    public String getPreCondition() {
        return preCondition;
    }

    public void setPreCondition(String preCondition) {
        this.preCondition = preCondition;
    }

    public List<ProgramVariableDeclaration> getProgramVariableDeclarations() {
        return programVariableDeclarations;
    }

    public List<FunctionDeclaration> getAbstractLocationSets() {
        return abstractLocationSets;
    }

    public List<FunctionDeclaration> getFunctionDeclarations() {
        return functionDeclarations;
    }

    public void setFunctionDeclarations(List<FunctionDeclaration> functionDeclarations) {
        this.functionDeclarations = functionDeclarations;
    }

    public List<PredicateDeclaration> getPredicateDeclarations() {
        return predicateDeclarations;
    }

    public Optional<File> getFile() {
        return file;
    }

    public String getMethodLevelContext() {
        return methodLevelContext;
    }

    public void setMethodLevelContext(String methodLevelContext) {
        this.methodLevelContext = methodLevelContext;
    }

    public void setProgram(String program) {
        this.program = program;
    }

    public void setAbstractLocationSets(List<FunctionDeclaration> abstractLocationSets) {
        this.abstractLocationSets = abstractLocationSets;
    }

    public void setPredicateDeclarations(List<PredicateDeclaration> predicateDeclarations) {
        this.predicateDeclarations = predicateDeclarations;
    }

    public void setProgramVariableDeclarations(
            List<ProgramVariableDeclaration> programVariableDeclarations) {
        this.programVariableDeclarations = programVariableDeclarations;
    }

    public List<PredicateInstantiation> getPredicateInstantiations() {
        return predicateInstantiations;
    }

    public void setPredicateInstantiations(List<PredicateInstantiation> predicateInstantiations) {
        this.predicateInstantiations = predicateInstantiations;
    }

    public List<FunctionInstantiation> getFunctionInstantiations() {
        return functionInstantiations;
    }

    public void setFunctionInstantiations(List<FunctionInstantiation> functionInstantiations) {
        this.functionInstantiations = functionInstantiations;
    }

    public boolean isSaved() {
        return file.isPresent();
    }

    public void setFile(File file) {
        this.file = Optional.of(file);
    }

    public String toXml() throws JAXBException {
        final JAXBContext context = JAXBContext.newInstance(AEInstantiationModel.class);
        final Marshaller m = context.createMarshaller();
        m.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);

        final ByteArrayOutputStream stream = new ByteArrayOutputStream();
        m.marshal(this, stream);
        return new String(stream.toByteArray());
    }

    /**
     * Parses an {@link AEInstantiationModel} from the given XML string.
     * 
     * @param xml The XML code.
     * @return The {@link AEInstantiationModel}.
     * @throws JAXBException If a problem occurred while unmarshalling.
     * @throws SAXException  If there is a validation error (XSD format not met).
     */
    public static AEInstantiationModel fromXml(String xml) throws JAXBException, SAXException {
        final JAXBContext jaxbContext = JAXBContext.newInstance(AEInstantiationModel.class);
        final Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
        final SchemaFactory sf = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
        final Schema schema = sf.newSchema(AEInstantiationModel.class.getResource(SCHEMA_PATH));
        jaxbUnmarshaller.setSchema(schema);

        return (AEInstantiationModel) jaxbUnmarshaller.unmarshal(new StringReader(xml));
    }

    /**
     * Returns true an {@link AEInstantiationModel} if the given file has the
     * {@link #AE_INSTANTIATION_FILE_ENDING} and can be loaded and parsed as
     * {@link AEInstantiationModel} XML file.
     * 
     * @param file The file to check.
     * @return An {@link AEInstantiationModel} iff the file could be verified to be
     *         an {@link AEInstantiationModel} file, otherwise an empty
     *         {@link Optional}.
     */
    public static Optional<AEInstantiationModel> isRelationalModelFile(File file) {
        if (!fileHasAEModelEnding(file)) {
            return Optional.empty();
        }

        try {
            return Optional.of(fromXml(new String(Files.readAllBytes(file.toPath()))));
        } catch (SAXException | JAXBException exc) {
        } catch (IOException exc) {
            exc.printStackTrace();
        }

        return Optional.empty();
    }

    /**
     * Checks if the given file has the {@link #AE_INSTANTIATION_FILE_ENDING}
     * ending.
     * 
     * @param file The file to check.
     * @return true iff the given file has the {@link #AE_INSTANTIATION_FILE_ENDING}
     *         ending.
     */
    public static boolean fileHasAEModelEnding(File file) {
        return file.getName().endsWith(AE_INSTANTIATION_FILE_ENDING);
    }

    /**
     * Populates the given {@link Services} object with function and program
     * variable symbols corresponding to the definitions in this model.
     * 
     * @param services The {@link Services} object to populate.
     * @throws RuntimeException If a name is already present, or a sort not known.
     */
    public void fillNamespacesFromModel(final Services services) {
        getAbstractLocationSets().forEach(loc -> loc.checkAndRegister(services));
        getProgramVariableDeclarations().forEach(pv -> pv.checkAndRegister(services));
        getPredicateDeclarations().forEach(pred -> pred.checkAndRegister(services));
        getFunctionDeclarations().forEach(pred -> pred.checkAndRegister(services));
    }

    /**
     * Populates the given {@link Services} object with function and program
     * variable symbols corresponding to the definitions in this model. Returns
     * false if an error occurred, true otherwise.
     * 
     * @param services The {@link Services} object to populate.
     * @return false if an error occurred, true otherwise.
     */
    public boolean tryFillNamespacesFromModel(final Services services) {
        try {
            fillNamespacesFromModel(services);
            return true;
        } catch (RuntimeException exc) {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return Objects.hash(program, methodLevelContext, preCondition, postCondition,
                predicateDeclarations, functionDeclarations, abstractLocationSets,
                programVariableDeclarations, predicateInstantiations, functionInstantiations);
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && obj instanceof AEInstantiationModel
                && ((AEInstantiationModel) obj).hashCode() == this.hashCode();
    }
}
