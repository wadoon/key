package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Implements the 'Heap' Positioning strategy for InsertionTerms
 * The terms get written in the lines where the contained heaps originate from
 */
public class HeapPositioner extends InsPositionProvider{
    private final boolean continueOnError;

    public HeapPositioner(Services svc, Proof proof, Node node, boolean continueOnError) {
        super(svc, proof, node);

        this.continueOnError = continueOnError;
    }

    public static List<HeapReference> ListHeaps(Term t, boolean distinct) throws InternTransformException {
        var result = new ArrayList<HeapReference>();

        if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {
            var updates = listHeapUpdates(t.sub(0));
            result.add(new HeapReference(updates));
        }

        for (var sub: t.subs()) {
            result.addAll(ListHeaps(sub, false));
        }

        if (distinct) {
            var dist = new ArrayList<HeapReference>();
            for (var h: result) {
                if (dist.stream().noneMatch(p -> p.heapEquals(h))) {
                    dist.add(h);
                }
            }
            result = dist;
        }

        return result;
    }

    public static List<HeapReference.HeapUpdate> listHeapUpdates(Term t) throws InternTransformException {

        if (!t.sort().name().toString().equals("Heap")) {
            throw new InternTransformException("Not a heap");
        }

        var result = new ArrayList<HeapReference.HeapUpdate>();

        if (t.op().name().toString().equals("store")) {
            result.addAll(listHeapUpdates(t.sub(0)));
            result.add(HeapReference.newStoreUpdate(t));
            return result;
        } else if (t.op().name().toString().equals("anon")) {
            result.addAll(listHeapUpdates(t.sub(0)));
            result.add(HeapReference.newAnonUpdate(t));
            return result;
        } else if (t.op() instanceof LocationVariable) {
            result.add(HeapReference.newHeap(t));
            return result;
        } else if (t.op() instanceof Function && t.arity() == 0) {
            result.add(HeapReference.newHeap(t));
            return result;
        } else {
            throw new InternTransformException("unknown heap op");
        }
    }

    public Optional<Integer> GetTermHeapPosition(Term t) {
        try {
            if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {
                return Optional.of(getPosition(null, t).Line);
            } else {
                return Optional.empty();
            }
        } catch (InternTransformException | TransformException e) {
            return Optional.empty();
        }
    }

    public InsertionPosition getActiveStatementPosition(URI fileUri) throws InternTransformException, TransformException {

        for (Node cur = this.node; cur != null; cur = cur.parent()) {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                PositionInfo pi = activeStatement.getPositionInfo();
                if (pi == PositionInfo.UNDEFINED) continue;
                if (pi.getURI() == PositionInfo.UNKNOWN_URI) continue;

                int line = pi.getStartPosition().getLine() + 1;
                int indent = getLineIndent(pi.getURI(), line);

                return new InsertionPosition(line, indent);
            }
        }

        // fallback (?) use method-start directly

        int endLine = getMethodPositionMap().getStartPosition().getLine() + 1;
        int endIndent = getLineIndent(fileUri, endLine);

        return new InsertionPosition(endLine, endIndent);
    }

    @Override
    public InsertionPosition getPosition(URI fileUri, InsertionTerm iterm) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        if (iterm.Type == InsertionType.ASSIGNABLE) {
            var line = methodPosition.getEndPosition().getLine();
            var indent = getLineIndent(fileUri, line);
            return new InsertionPosition(line, indent);
        }

        return getPosition(fileUri, iterm.Term);
    }

    public InsertionPosition getPosition(URI fileUri, Term term) throws InternTransformException, TransformException {
        var heaps = ListHeaps(term, false).stream().filter(p -> p.getLineNumber().isPresent()).collect(Collectors.toList());

        if (heaps.size() == 0) {
            return getActiveStatementPosition(fileUri);
        }

        //noinspection OptionalGetWithoutIsPresent
        int line = heaps.stream().map(p -> p.getLineNumber().get()).max(Integer::compare).get();

        line += 1; // should be _after_ this line (that changed the heap)

        var indent = getLineIndent(fileUri, line);


        return new InsertionPosition(line, indent);
    }

    @Override
    public Integer getOldPos() throws TransformException {
        return getMethodPositionMap().getStartPosition().getLine() + 1;
    }
}
