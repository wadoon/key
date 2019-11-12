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
package de.uka.ilkd.key.gui.abstractexecution.relational.model;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

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

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(namespace = "http://www.key-project.org/abstractexecution")
@XmlType(propOrder = {"programOne", "programTwo", "abstractLocationSets", "predicateDeclarations", "programVariableDeclarations"})
public class AERelationalModel {
    public static final AERelationalModel EMPTY_MODEL = new AERelationalModel();
    
    private String programOne = "";
    private String programTwo = "";
    private String postCondition = "";
    private List<String> abstractLocationSets = new ArrayList<>();
    private List<PredicateDeclaration> predicateDeclarations = new ArrayList<>();
    private List<ProgramVariableDeclaration> programVariableDeclarations = new ArrayList<>();
    @XmlTransient
    private Optional<File> file = Optional.empty();

    public AERelationalModel(final String programOne, final String programTwo,
            final String postCondition,
            final List<String> abstractLocationSets,
            final List<PredicateDeclaration> predicateDeclarations,
            final List<ProgramVariableDeclaration> programVariableDeclarations) {
        this.programOne = programOne;
        this.programTwo = programTwo;
        this.postCondition = postCondition;
        this.abstractLocationSets = abstractLocationSets;
        this.predicateDeclarations = predicateDeclarations;
        this.programVariableDeclarations = programVariableDeclarations;
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

    @XmlElementWrapper(name="programVariables")
    @XmlElement(name = "programVariable")
    public List<ProgramVariableDeclaration> getProgramVariableDeclarations() {
        return programVariableDeclarations;
    }
    
    @XmlElementWrapper(name="locationSets")
    @XmlElement(name = "locationSet")
    public List<String> getAbstractLocationSets() {
        return abstractLocationSets;
    }

    @XmlElementWrapper(name="predicates")
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
    
    public void setAbstractLocationSets(List<String> abstractLocationSets) {
        this.abstractLocationSets = abstractLocationSets;
    }

    public void setPredicateDeclarations(List<PredicateDeclaration> predicateDeclarations) {
        this.predicateDeclarations = predicateDeclarations;
    }

    public void setProgramVariableDeclarations(
            List<ProgramVariableDeclaration> programVariableDeclarations) {
        this.programVariableDeclarations = programVariableDeclarations;
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

    public static AERelationalModel fromXml(String xml) throws JAXBException {
        final JAXBContext jaxbContext = JAXBContext.newInstance(AERelationalModel.class);
        final Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
        return (AERelationalModel) jaxbUnmarshaller.unmarshal(new StringReader(xml));
    }

}
