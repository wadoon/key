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
package de.uka.ilkd.key.abstractexecution.refinity.model;

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
import java.util.stream.Collectors;
import java.util.stream.Stream;

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

import de.uka.ilkd.key.java.Services;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(namespace = "http://www.key-project.org/abstractexecution")
@XmlType(propOrder = { "programOne", "programTwo", "methodLevelContext", "abstractLocationSets",
        "functionDeclarations", "predicateDeclarations", "programVariableDeclarations" })
@XmlAccessorType(value = XmlAccessType.FIELD)
public class AERelationalModel {
    private static final String AE_MODEL_FILE_ENDING = ".aer";
    private static final String SCHEMA_PATH = "/de/uka/ilkd/key/refinity/schema1.xsd";

    @XmlElement(name = "programOne")
    private String programOne = "";

    @XmlElement(name = "programTwo")
    private String programTwo = "";

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

    @XmlTransient
    private Optional<File> file = Optional.empty();

    public static AERelationalModel defaultModel() {
        final String postCondition = "\\result_1==\\result_2";
        final List<FunctionDeclaration> abstractLocationSets = Collections
                .singletonList(new FunctionDeclaration("relevant", "LocSet"));
        final List<NullarySymbolDeclaration> relevantVarsOne = //
                Collections.singletonList(abstractLocationSets.get(0));
        final List<NullarySymbolDeclaration> relevantVarsTwo = //
                Collections.singletonList(abstractLocationSets.get(0));

        return new AERelationalModel("", "", "", postCondition, abstractLocationSets,
                Collections.emptyList(), Collections.emptyList(), Collections.emptyList(),
                relevantVarsOne, relevantVarsTwo);
    }

    public AERelationalModel(final String programOne, final String programTwo,
            String methodLevelContext, final String postCondition,
            final List<FunctionDeclaration> abstractLocationSets,
            final List<FunctionDeclaration> functionDeclarations,
            final List<PredicateDeclaration> predicateDeclarations,
            final List<ProgramVariableDeclaration> programVariableDeclarations,
            final List<NullarySymbolDeclaration> relevantVarsOne,
            final List<NullarySymbolDeclaration> relevantVarsTwo) {
        this.programOne = programOne;
        this.programTwo = programTwo;
        this.methodLevelContext = methodLevelContext;
        this.postCondition = postCondition;
        this.abstractLocationSets = abstractLocationSets;
        this.functionDeclarations = functionDeclarations;
        this.predicateDeclarations = predicateDeclarations;
        this.programVariableDeclarations = programVariableDeclarations;
        setRelevantVarsOne(relevantVarsOne);
        setRelevantVarsTwo(relevantVarsTwo);
    }

    AERelationalModel() {
    }

    public String getProgramOne() {
        return programOne;
    }

    public String getProgramTwo() {
        return programTwo;
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

    public List<NullarySymbolDeclaration> getRelevantVarsOne() {
        return getRelevantVars(NullarySymbolDeclaration::getRelevantOne);
    }

    public List<NullarySymbolDeclaration> getRelevantVarsTwo() {
        return getRelevantVars(NullarySymbolDeclaration::getRelevantTwo);
    }

    public List<NullarySymbolDeclaration> getRelevantVars(
            java.util.function.Function<NullarySymbolDeclaration, Integer> relValGetter) {
        return getRelevantVars(relValGetter, getAbstractLocationSets(),
                getProgramVariableDeclarations());
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

    private static List<NullarySymbolDeclaration> getRelevantVars(
            java.util.function.Function<NullarySymbolDeclaration, Integer> relValGetter,
            final List<FunctionDeclaration> abstrLocsets,
            final List<ProgramVariableDeclaration> abstrPVDecls) {
        return Stream.concat(abstrLocsets.stream(), abstrPVDecls.stream())
                .filter(loc -> relValGetter.apply(loc) > -1)
                .sorted((loc1, loc2) -> relValGetter.apply(loc1) - relValGetter.apply(loc2))
                .collect(Collectors.toList());
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
        return Objects.hash(programOne, programTwo, methodLevelContext, preCondition, postCondition,
                predicateDeclarations, functionDeclarations, abstractLocationSets,
                programVariableDeclarations);
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && obj instanceof AERelationalModel
                && ((AERelationalModel) obj).hashCode() == this.hashCode();
    }
}
