package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;
import lombok.Data;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (15.08.17)
 */
@Data
public class SubstituteExpression extends Expression<ScriptLanguageParser.ExprSubstContext> {
    private Expression sub;
    private Map<String, Expression> substitution = new LinkedHashMap<>();

    @Override
    public boolean hasMatchExpression() {
        return sub.hasMatchExpression();
    }

    @Override
    public int getPrecedence() {
        return Operator.SUBST.precedence();
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expression copy() {
        SubstituteExpression se = new SubstituteExpression();
        se.sub = sub.copy();
        se.substitution = new LinkedHashMap<>(substitution);
        se.setRuleContext(this.ruleContext);
        return se;
    }

    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        Type t = sub.getType(signature);
        if (!TypeFacade.isTerm(t)) {
            throw new NotWelldefinedException("Term<?> expected, got " + t.symbol(), this);
        }
        return TypeFacade.ANY_TERM;
    }

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getSub()};
    }
}
