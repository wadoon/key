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

import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.proof.Node;

/**
 * Describes a "hole" left by lazy symbolic execution of a while loop.
 * Corresponds roughly to the information available to instantiations of the
 * "lazyLoop" taclet.
 *
 * @author Dominic Steinhöfel
 */
public class LoopHole {
    private final int loopNum;
    private final String pathCondPlaceholder;
    private final String symbStorePlaceholder;
    private final Node proofNode;
    private final While loopStatement;

    /**
     * Constructor for test cases / GUI development. Don't use for real proofs!
     *
     * @param loopNum
     * @param pathCondPlaceholder
     * @param symbStorePlaceholder
     */
    public LoopHole(int loopNum, String pathCondPlaceholder,
            String symbStorePlaceholder) {
        this(loopNum, pathCondPlaceholder, symbStorePlaceholder, null, null);
    }

    /**
     * Creates a new {@link LoopHole}.
     *
     * @param loopNum
     *            Sequent number of the loop. Relevant for displaying
     *            something digestible to the user and for proof I/O.
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
     * @param loopStatement
     *            The {@link While} loop statement on which the lazy symbolic
     *            execution rule has been applied.
     */
    public LoopHole(int loopNum, String pathCondPlaceholder,
            String symbStorePlaceholder, Node proofNode, While loopStatement) {
        this.loopNum = loopNum;
        this.pathCondPlaceholder = pathCondPlaceholder;
        this.symbStorePlaceholder = symbStorePlaceholder;
        this.proofNode = proofNode;
        this.loopStatement = loopStatement;
    }

    public int getLoopNum() {
        return loopNum;
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

    public While getLoopStatement() {
        return loopStatement;
    }

    /**
     * @return a short description of the {@link LoopHole} using the sequence
     *         number. Only for displaying something to the user.
     */
    public String instTabTitle() {
        return "Loop " + loopNum;
    }

    @Override
    public String toString() {
        return String.format("Loop %d: (%s, %s)", loopNum, pathCondPlaceholder,
            symbStorePlaceholder);
    }
}