package recoder.java;

public class SingleLineComment extends Comment {
    private static final long serialVersionUID = -1462907890949586507L;

    public SingleLineComment() {
    }

    public SingleLineComment(String text) {
        super(text);
    }

    protected SingleLineComment(SingleLineComment proto) {
        super(proto);
    }

    public SingleLineComment deepClone() {
        return new SingleLineComment(this);
    }

    public void accept(SourceVisitor v) {
        v.visitSingleLineComment(this);
    }
}
