package recoder.bytecode;

import recoder.abstraction.AnnotationUse;
import recoder.abstraction.ElementValuePair;

import java.util.List;

public class AnnotationUseInfo implements AnnotationUse {
    protected List<ElementValuePair> elementValuePairs;

    protected String fullAnnotationTypeName;

    public AnnotationUseInfo(String fullName, List<ElementValuePair> evpl) {
        this.elementValuePairs = evpl;
        this.fullAnnotationTypeName = fullName;
    }

    public List<ElementValuePair> getElementValuePairs() {
        return this.elementValuePairs;
    }

    private String getParamStr() {
        StringBuffer res = new StringBuffer();
        boolean first = true;
        for (ElementValuePair evp : this.elementValuePairs) {
            if (!first)
                res.append(",");
            first = false;
            res.append(evp.toString());
        }
        return res.toString();
    }

    public String toString() {
        return "@" + getFullReferencedName() + "(" + getParamStr() + ")";
    }

    public String getFullReferencedName() {
        return this.fullAnnotationTypeName;
    }

    public String getReferencedName() {
        return this.fullAnnotationTypeName.substring(this.fullAnnotationTypeName.lastIndexOf('.') + 1);
    }
}
