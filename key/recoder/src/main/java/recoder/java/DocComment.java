package recoder.java;

public class DocComment extends Comment {
    private static final long serialVersionUID = 621277739856803262L;

    public DocComment() {
        setPrefixed(true);
    }

    public DocComment(String text) {
        super(text, true);
    }

    protected DocComment(DocComment proto) {
        super(proto);
    }

    public DocComment deepClone() {
        return new DocComment(this);
    }

    public TagInfo createTagInfo() {
        return new TagInfo(this);
    }

    public void accept(SourceVisitor v) {
        v.visitDocComment(this);
    }
}
