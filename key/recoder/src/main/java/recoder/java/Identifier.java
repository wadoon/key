package recoder.java;

public class Identifier extends JavaProgramElement implements TerminalProgramElement {
    private static final long serialVersionUID = 4261793022531143013L;

    protected NonTerminalProgramElement parent;

    protected String id;

    public Identifier() {
        this.id = "";
    }

    public Identifier(String text) {
        setText(text);
    }

    protected Identifier(Identifier proto) {
        super(proto);
        this.id = proto.id;
    }

    public Identifier deepClone() {
        return new Identifier(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public NonTerminalProgramElement getParent() {
        return this.parent;
    }

    public void setParent(NonTerminalProgramElement p) {
        this.parent = p;
    }

    public final String getText() {
        return this.id;
    }

    protected void setText(String text) {
        if (!Character.isJavaIdentifierStart(text.charAt(0)))
            throw new IllegalArgumentException(text + " is not a valid Java identifier");
        for (int i = text.length() - 1; i >= 1; i--) {
            if (!Character.isJavaIdentifierPart(text.charAt(i)))
                throw new IllegalArgumentException(text + " is not a valid Java identifier");
        }
        this.id = text.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitIdentifier(this);
    }
}
