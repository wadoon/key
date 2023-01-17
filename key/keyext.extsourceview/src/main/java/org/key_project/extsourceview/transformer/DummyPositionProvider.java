package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;

import java.util.Optional;

public class DummyPositionProvider extends InsPositionProvider {
    public DummyPositionProvider() {
        super(null, null, null);
    }

    @Override
    public InsertionPosition getPosition(Sequent s, InsertionTerm term) throws TransformException, InternTransformException {
        return new InsertionPosition(1, 1, 0);
    }

    @Override
    public Optional<Integer> GetTermHeapPosition(Sequent s, Term t, InsertionType itype) {
        return Optional.empty();
    }

    @Override
    public Integer getOldPos() {
        return 1;
    }

    @Override
    public boolean heapPosAreEqual(int p1, int p2) {
        return p1 == p2;
    }
}
