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
package de.uka.ilkd.key.abstractexecution.relational.model;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;
import javax.xml.bind.annotation.XmlType;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;

import org.xml.sax.SAXException;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(namespace = "http://www.key-project.org/abstractexecution")
@XmlType(propOrder = { "programOne", "programTwo", "methodDeclsOne", "methodDeclsTwo",
        "abstractLocationSets", "predicateDeclarations", "programVariableDeclarations" })
public class AERelationalModel {
    private static final String AE_MODEL_FILE_ENDING = ".aer";
    public static final AERelationalModel EMPTY_MODEL = new AERelationalModel();
    private static final String SCHEMA_PATH = "/de/uka/ilkd/key/abstractexecution/relational/schema1.xsd";

    private String programOne = "";
    private String programTwo = "";
    private String postCondition = "";
    private List<PredicateDeclaration> predicateDeclarations = new ArrayList<>();
    private List<AbstractLocsetDeclaration> abstractLocationSets = new ArrayList<>();
    private List<ProgramVariableDeclaration> programVariableDeclarations = new ArrayList<>();
    private Optional<File> file = Optional.empty();
    private List<MethodDeclaration> methodDeclarationsOne = new ArrayList<>();
    private List<MethodDeclaration> methodDeclarationsTwo = new ArrayList<>();

    public AERelationalModel(final String programOne, final String programTwo,
            final String postCondition, final List<AbstractLocsetDeclaration> abstractLocationSets,
            final List<PredicateDeclaration> predicateDeclarations,
            final List<ProgramVariableDeclaration> programVariableDeclarations,
            final List<NullarySymbolDeclaration> relevantVarsOne,
            final List<NullarySymbolDeclaration> relevantVarsTwo) {
        this.programOne = programOne;
        this.programTwo = programTwo;
        this.postCondition = postCondition;
        this.abstractLocationSets = abstractLocationSets;
        this.predicateDeclarations = predicateDeclarations;
        this.programVariableDeclarations = programVariableDeclarations;

        setRelevantVarsOne(relevantVarsOne);
        setRelevantVarsTwo(relevantVarsTwo);
    }

    AERelationalModel() {
    }

    @XmlElement(name = "programOne")
    public String getProgramOne() {
        return programOne;
    }

    @XmlElement(name = "programTwo")
    public String getProgramTwo() {
        return programTwo;
    }

    @XmlAttribute(name = "postCondition")
    public String getPostCondition() {
        return postCondition;
    }

    public void setPostCondition(String postCondition) {
        this.postCondition = postCondition;
    }

    @XmlElementWrapper(name = "programVariables")
    @XmlElement(name = "programVariable")
    public List<ProgramVariableDeclaration> getProgramVariableDeclarations() {
        return programVariableDeclarations;
    }

    @XmlElementWrapper(name = "locationSets")
    @XmlElement(name = "locationSet")
    public List<AbstractLocsetDeclaration> getAbstractLocationSets() {
        return abstractLocationSets;
    }

    @XmlElementWrapper(name = "predicates")
    @XmlElement(name = "predicate")
    public List<PredicateDeclaration> getPredicateDeclarations() {
        return predicateDeclarations;
    }

    @XmlTransient
    public List<NullarySymbolDeclaration> getRelevantVarsOne() {
        return getRelevantVars(NullarySymbolDeclaration::getRelevantOne);
    }

    @XmlTransient
    public List<NullarySymbolDeclaration> getRelevantVarsTwo() {
        return getRelevantVars(NullarySymbolDeclaration::getRelevantTwo);
    }

    @XmlElementWrapper(name = "methodDeclsOne")
    @XmlElement(name = "methodDecl")
    public List<MethodDeclaration> getMethodDeclsOne() {
        return methodDeclarationsOne;
    }

    @XmlElementWrapper(name = "methodDeclsTwo")
    @XmlElement(name = "methodDecl")
    public List<MethodDeclaration> getMethodDeclsTwo() {
        return methodDeclarationsTwo;
    }

    public List<NullarySymbolDeclaration> getRelevantVars(
            java.util.function.Function<NullarySymbolDeclaration, Integer> relValGetter) {
        return Stream
                .concat(getAbstractLocationSets().stream(),
                        getProgramVariableDeclarations().stream())
                .filter(loc -> relValGetter.apply(loc) > -1)
                .sorted((loc1, loc2) -> relValGetter.apply(loc1) - relValGetter.apply(loc2))
                .collect(Collectors.toList());
    }

    @XmlTransient
    public Optional<File> getFile() {
        return file;
    }

    public void setRelevantVarsOne(List<NullarySymbolDeclaration> relevantVarsOne) {
        getProgramVariableDeclarations()
                .forEach(pv -> pv.setRelevantOne(relevantVarsOne.indexOf(pv)));
        getAbstractLocationSets().forEach(pv -> pv.setRelevantOne(relevantVarsOne.indexOf(pv)));
    }

    public void setRelevantVarsTwo(List<NullarySymbolDeclaration> relevantVarsTwo) {
        getProgramVariableDeclarations()
                .forEach(pv -> pv.setRelevantTwo(relevantVarsTwo.indexOf(pv)));
        getAbstractLocationSets().forEach(pv -> pv.setRelevantTwo(relevantVarsTwo.indexOf(pv)));
    }

    public void setProgramOne(String programOne) {
        this.programOne = programOne;
    }

    public void setProgramTwo(String programTwo) {
        this.programTwo = programTwo;
    }

    public void setAbstractLocationSets(List<AbstractLocsetDeclaration> abstractLocationSets) {
        this.abstractLocationSets = abstractLocationSets;
    }

    public void setPredicateDeclarations(List<PredicateDeclaration> predicateDeclarations) {
        this.predicateDeclarations = predicateDeclarations;
    }

    public void setProgramVariableDeclarations(
            List<ProgramVariableDeclaration> programVariableDeclarations) {
        this.programVariableDeclarations = programVariableDeclarations;
    }

    public void setMethodDeclarationsOne(List<MethodDeclaration> methodDeclarationsOne) {
        this.methodDeclarationsOne = methodDeclarationsOne;
    }

    public void setMethodDeclarationsTwo(List<MethodDeclaration> methodDeclarationsTwo) {
        this.methodDeclarationsTwo = methodDeclarationsTwo;
    }

    public boolean isSaved() {
        return file.isPresent();
    }

    public void setFile(File file) {
        this.file = Optional.of(file);
    }

    public String toXml() throws JAXBException {
        final JAXBContext context = JAXBContext.newInstance(AERelationalModel.class);
        final Marshaller m = context.createMarshaller();
        m.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);

        final ByteArrayOutputStream stream = new ByteArrayOutputStream();
        m.marshal(this, stream);
        return new String(stream.toByteArray());
    }

    /**
     * Parses an {@link AERelationalModel} from the given XML string.
     * 
     * @param xml The XML code.
     * @return The {@link AERelationalModel}.
     * @throws JAXBException If a problem occurred while unmarshalling.
     * @throws SAXException  If there is a validation error (XSD format not met).
     */
    public static AERelationalModel fromXml(String xml) throws JAXBException, SAXException {
        final JAXBContext jaxbContext = JAXBContext.newInstance(AERelationalModel.class);
        final Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
        final SchemaFactory sf = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
        final Schema schema = sf.newSchema(AERelationalModel.class.getResource(SCHEMA_PATH));
        jaxbUnmarshaller.setSchema(schema);

        return (AERelationalModel) jaxbUnmarshaller.unmarshal(new StringReader(xml));
    }

    /**
     * Returns true an {@link AERelationalModel} if the given file has the
     * {@link #AE_MODEL_FILE_ENDING} and can be loaded and parsed as
     * {@link AERelationalModel} XML file.
     * 
     * @param file The file to check.
     * @return An {@link AERelationalModel} iff the file could be verified to be an
     *         {@link AERelationalModel} file, otherwise an empty {@link Optional}.
     */
    public static Optional<AERelationalModel> isRelationalModelFile(File file) {
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
     * Checks if the given file has the {@link #AE_MODEL_FILE_ENDING} ending.
     * 
     * @param file The file to check.
     * @return true iff the given file has the {@link #AE_MODEL_FILE_ENDING} ending.
     */
    public static boolean fileHasAEModelEnding(File file) {
        return file.getName().endsWith(AE_MODEL_FILE_ENDING);
    }

}
