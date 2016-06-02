package org.key_project.common.core.logic;

import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

public interface SpecialSorts {

    public class SpecialSort implements Sort {

        private final Name name;

        public SpecialSort(Name name) {
            this.name = name;
        }

        @Override
        public Name name() {
            return name;
        }

        @Override
        public boolean extendsTrans(Sort s, TermServices services) {
            return s == this;
        }

        @Override
        public boolean isAbstract() {
            return false;
        }

        @Override
        public ImmutableSet<Sort> extendsSorts(TermServices services) {
            return DefaultImmutableSet.<Sort>nil();
        }

        @Override
        public SortDependingFunction getCastSymbol(TermServices services) {
            throw new UnsupportedOperationException("Cast not available for sort: "+name);
        }

        @Override
        public SortDependingFunction getInstanceofSymbol(
                TermServices services) {
            throw new UnsupportedOperationException("Cast not available for sort: "+name);
        }

        @Override
        public SortDependingFunction getExactInstanceofSymbol(
                TermServices services) {
            throw new UnsupportedOperationException("Cast not available for sort: "+name);
        }

        @Override
        public String declarationString() {
            return name.toString();
        }

    }

    /**
     * Formulas are represented as "terms" of this sort.
     */
    Sort FORMULA = new SpecialSort(new Name("Formula"));
    
    /**
     * Updates are represented as "terms" of this sort.
     */
    Sort UPDATE = new SpecialSort(new Name("Update"));
    /**
     * Term labels are represented as "terms" of this sort.
     */
    Sort TERMLABEL = new SpecialSort(new Name("TermLabel"));

    /**
     * Any is a supersort of all sorts.
     */
    Sort ANY = new SpecialSort(new Name("any"));

}
