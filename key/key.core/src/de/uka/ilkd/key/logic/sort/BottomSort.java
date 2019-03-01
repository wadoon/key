package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


/**
 * This sort is used for term matching of matching expressions in the ProofScriptDebugger
 * for terms represented by a specific schemavariable
 * see {@NullSort}
 */
public final class BottomSort implements Sort  {

    public static final Name NAME = new Name("Bottom");
    public static final BottomSort INSTANCE = new BottomSort();

    private BottomSort() {}

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public ImmutableSet<Sort> extendsSorts() {
        throw new UnsupportedOperationException(
                "BottomSort.extendsSorts() cannot be supported");
    }

    @Override
    public ImmutableSet<Sort> extendsSorts(Services services) {
        assert services != null;

        ImmutableSet<Sort> returnValue = DefaultImmutableSet.nil();
        services.getNamespaces().sorts().allElements().forEach(sort -> returnValue.add(sort));

        return returnValue;
    }


    @Override
    public boolean extendsTrans(Sort sort) {
        return true;
    }

    @Override
    public boolean isAbstract() {
        return false;
    }

    @Override
    public final SortDependingFunction getCastSymbol(TermServices services) {
        SortDependingFunction result
                = SortDependingFunction.getFirstInstance(CAST_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }


    @Override
    public final SortDependingFunction getInstanceofSymbol(TermServices services) {
        SortDependingFunction result
                = SortDependingFunction.getFirstInstance(INSTANCE_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }

    @Override
    public final SortDependingFunction getExactInstanceofSymbol(TermServices services) {
        SortDependingFunction result
                = SortDependingFunction.getFirstInstance(EXACT_INSTANCE_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }


    @Override
    public final String toString() {
        return NAME.toString();
    }

    @Override
    public String declarationString() {
        return NAME.toString();
    }
}