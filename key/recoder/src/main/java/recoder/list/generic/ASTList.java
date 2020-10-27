package recoder.list.generic;

import java.util.List;

public interface ASTList<E extends recoder.java.SourceElement> extends List<E> {
    ASTList<E> deepClone();

    void trimToSize();
}
