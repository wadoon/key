package recoder.java;

import recoder.ModelException;
import recoder.list.generic.ASTList;

public abstract class JavaProgramElement extends JavaSourceElement implements ProgramElement {
    protected ASTList<Comment> comments;

    public JavaProgramElement() {
    }

    protected JavaProgramElement(JavaProgramElement proto) {
        super(proto);
        if (proto.comments != null)
            this.comments = proto.comments.deepClone();
    }

    public ASTList<Comment> getComments() {
        return this.comments;
    }

    public void setComments(ASTList<Comment> list) {
        this.comments = list;
        if (this.comments != null)
            for (int i = 0; i < this.comments.size(); i++)
                this.comments.get(i).setParent(this);
    }

    public void validate() throws ModelException {
    }
}
