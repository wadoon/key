// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.lazyse;

import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.proof.Node;

/**
 * Describes a "hole" left by lazy symbolic execution of an
 * {@link AbstractPlaceholderStatement}.
 *
 * @author Dominic Steinhöfel
 */
public class AbstractExecutionHole {
    private final int abstractProgramNum;
    private final String pathCondPlaceholder;
    private final String symbStorePlaceholder;
    private final Node proofNode;
    private final AbstractPlaceholderStatement loopStatement;

    /**
     * Constructor for test cases / GUI development. Don't use for real proofs!
     */
    public AbstractExecutionHole(int abstractProgramNum, String pathCondPlaceholder,
            String symbStorePlaceholder) {
        this(abstractProgramNum, pathCondPlaceholder, symbStorePlaceholder, null, null);
    }

    /**
     * Creates a new {@link AbstractExecutionHole}.
     *
     * @param abstractProgramNum
     *            Sequent number of the loop. Relevant for displaying something
     *            digestible to the user and for proof I/O.
     * @param pathCondPlaceholder
     *            Name of the Skolem function serving as a placeholder for a
     *            loop invariant / path condition.
     * @param symbStorePlaceholder
     *            Name of the Skolem function serving as a placeholder for the
     *            update / symbolic store, in the case of a loop mainly for
     *            anonymization.
     * @param proofNode
     *            The {@link Node} where the lazy symbolic execution rule has
     *            been applied.
     * @param abstractPlaceholderStatement
     *            The {@link AbstractPlaceholderStatement} on which the lazy
     *            symbolic execution rule has been applied.
     */
    public AbstractExecutionHole(int abstractProgramNum, String pathCondPlaceholder,
            String symbStorePlaceholder, Node proofNode,
            AbstractPlaceholderStatement abstractPlaceholderStatement) {
        this.abstractProgramNum = abstractProgramNum;
        this.pathCondPlaceholder = pathCondPlaceholder;
        this.symbStorePlaceholder = symbStorePlaceholder;
        this.proofNode = proofNode;
        this.loopStatement = abstractPlaceholderStatement;
    }

    public int getAbstractProgramNum() {
        return abstractProgramNum;
    }

    public String getPathCondPlaceholder() {
        return pathCondPlaceholder;
    }

    public String getSymbStorePlaceholder() {
        return symbStorePlaceholder;
    }

    public Node getProofNode() {
        return proofNode;
    }

    public AbstractPlaceholderStatement getAbstractPlaceholderStatement() {
        return loopStatement;
    }

    /**
     * @return a short description of the {@link AbstractExecutionHole} using
     *         the sequence number. Only for displaying something to the user.
     */
    public String instTabTitle() {
        return "Abstract Program " + abstractProgramNum;
    }

    @Override
    public String toString() {
        return String.format("Abstract Program %d: (%s, %s)", abstractProgramNum,
            pathCondPlaceholder, symbStorePlaceholder);
    }
}