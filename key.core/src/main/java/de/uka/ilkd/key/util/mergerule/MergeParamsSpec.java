package de.uka.ilkd.key.util.mergerule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.MergeContract;

import org.key_project.util.collection.ImmutableList;

/**
 * Specification of merge parameters for the creation of {@link MergeContract}s;
 *
 * @author Dominic Scheurer
 */
public record MergeParamsSpec(String latticeType, LocationVariable placeholder, ImmutableList<Term> predicates) {
}
