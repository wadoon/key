package recoder.list.generic;

import recoder.java.SourceElement;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

public class ASTArrayList<E extends SourceElement> extends ArrayList<E> implements ASTList<E> {
    private static final long serialVersionUID = 3179494289054893052L;

    public ASTArrayList() {
    }

    public ASTArrayList(Collection<E> c) {
        super(c);
    }

    public ASTArrayList(int initialCapacity) {
        super(initialCapacity);
    }

    public ASTArrayList(E initialItem) {
        this(1);
        add(initialItem);
    }

    public ASTArrayList<E> deepClone() {
        ASTArrayList<E> result = new ASTArrayList(size());
        Iterator<E> i = iterator();
        while (i.hasNext()) {
            SourceElement sourceElement = i.next().deepClone();
            result.add((E) sourceElement);
        }
        return result;
    }
}
