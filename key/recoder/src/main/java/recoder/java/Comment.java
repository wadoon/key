package recoder.java;

public class Comment extends JavaSourceElement {
    private static final long serialVersionUID = 5919865992017191460L;

    protected String text;

    protected boolean prefixed;
    protected ProgramElement parent;
    private boolean isContainerComment;

    public Comment() {
        this.text = "";
    }

    public Comment(String text) {
        setText(text);
    }

    public Comment(String text, boolean prefixed) {
        setText(text);
        setPrefixed(prefixed);
    }

    protected Comment(Comment proto) {
        super(proto);
        this.text = proto.text;
        this.prefixed = proto.prefixed;
    }

    public Comment deepClone() {
        return new Comment(this);
    }

    public boolean isPrefixed() {
        return this.prefixed;
    }

    public void setPrefixed(boolean prefixed) {
        this.prefixed = prefixed;
        this.isContainerComment = false;
    }

    public boolean isContainerComment() {
        return this.isContainerComment;
    }

    public void setContainerComment(boolean isContainerComment) {
        this.isContainerComment = isContainerComment;
        this.prefixed = false;
    }

    public ProgramElement getParent() {
        return this.parent;
    }

    public void setParent(ProgramElement p) {
        this.parent = p;
    }

    public String getText() {
        return this.text;
    }

    public void setText(String text) {
        this.text = text;
    }

    public void accept(SourceVisitor v) {
        v.visitComment(this);
    }
}
