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
@XmlType(propOrder = { "programOne", "programTwo", "abstractLocationSets", "predicateDeclarations",
        "programVariableDeclarations" })
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
    private List<NullarySymbolDeclaration> relevantVarsOne = new ArrayList<>();
    private List<NullarySymbolDeclaration> relevantVarsTwo = new ArrayList<>();

    @XmlTransient
    private Optional<File> file = Optional.empty();

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
        this.relevantVarsOne = relevantVarsOne;
        this.relevantVarsTwo = relevantVarsTwo;
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

    @XmlElementWrapper(name = "relevantVarsOne")
    @XmlElement(name = "relevantVar")
    public List<NullarySymbolDeclaration> getRelevantVarsOne() {
        return relevantVarsOne;
    }

    public void setRelevantVarsOne(List<NullarySymbolDeclaration> relevantVarsOne) {
        this.relevantVarsOne = relevantVarsOne;
    }

    @XmlElementWrapper(name = "relevantVarsTwo")
    @XmlElement(name = "relevantVar")
    public List<NullarySymbolDeclaration> getRelevantVarsTwo() {
        return relevantVarsTwo;
    }

    public void setRelevantVarsTwo(List<NullarySymbolDeclaration> relevantVarsTwo) {
        this.relevantVarsTwo = relevantVarsTwo;
    }

    public Optional<File> getFile() {
        return file;
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
