package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import org.key_project.util.ExtList;

import java.util.List;

public abstract class JumpStatement extends JavaStatement {
    /**
     * Jump statement.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain: Comments
     */
    public JumpStatement(ExtList children) {
        super(children);
    }

    public JumpStatement(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }
}