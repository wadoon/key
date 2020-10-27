package recoder.abstraction;

import java.util.List;

public interface AnnotationUse {
    List<? extends ElementValuePair> getElementValuePairs();
}
