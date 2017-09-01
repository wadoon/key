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

package de.tud.cs.se.ds.specstr.analyzer;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.rule.Rule;

/**
 * Finds {@link Node}s with application of a given {@link Rule} {@link Class}
 * (or subclasses of it) in the {@link Proof} tree.
 *
 * @author Dominic Steinhoefel
 */
public class RuleProofVisitor implements ProofVisitor {
    private Set<Node> result = new LinkedHashSet<>();
    private final Class<? extends Rule> searched;

    /**
     * Constructor.
     * 
     * @param searched
     *            The {@link Rule} {@link Class} that the {@link Proof} tree is
     *            searched for.
     */
    public RuleProofVisitor(Class<? extends Rule> searched) {
        this.searched = searched;
    }

    @Override
    public void visit(Proof proof, Node visitedNode) {
        if (visitedNode.getAppliedRuleApp() != null && searched
                .isInstance(visitedNode.getAppliedRuleApp().rule())) {
            result.add(visitedNode);
        }
    }

    /**
     * @return The found {@link Set} of {@link Node}s on which a {@link Rule} of
     *         the given type has been applied
     */
    public Set<Node> result() {
        return result;
    }

}
