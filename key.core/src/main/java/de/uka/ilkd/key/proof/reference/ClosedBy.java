package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Indicates that a branch has been closed by "reference" to another closed proof.
 *
 * @param proof The proof referenced.
 * @param node  The node referenced.
 * @author Arne Keller
 */
public record ClosedBy(Proof proof, Node node) {
}
