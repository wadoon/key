package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.NonNull;

import javax.annotation.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (22.05.18)
 */
@Data
@AllArgsConstructor
@NoArgsConstructor
public class LetStatement extends Statement<ScriptLanguageParser.LetStmtContext> {
    @NonNull
    private Expression expression;
    @Nullable
    private Statements body;

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getExpression(), getBody()};
    }

    @Override
    public LetStatement copy() {
        LetStatement ls = new LetStatement();
        ls.expression = expression.copy();
        ls.body = body.copy();
        return ls;
    }

    public boolean isBindGlobal() {
        return getBody() != null;
    }
}
