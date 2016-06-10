package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.Visitor;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;

public interface JavaDLVisitor extends Visitor<SourceElement, JavaDLVisitor, JavaDLTerm, NameAbstractionTable> {

}
