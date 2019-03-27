package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.TermValue;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.Expression;
import edu.kit.iti.formal.psdbg.parser.ast.SubstituteExpression;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class KeyEvaluator extends Evaluator<KeyData> {
    public KeyEvaluator(VariableAssignment assignments, GoalNode<KeyData> g) {
        super(assignments, g);
    }


    private Sort asKeySort(Type symbol, Goal g) {
        NamespaceSet global = g.proof().getServices().getNamespaces();
        Sort s = global.sorts().lookup(symbol.interpreterSort());
        if (s != null)
            return s;
        return g.getLocalNamespaces().sorts().lookup(symbol.interpreterSort());
    }

    @Override
    public Value visit(SubstituteExpression expr) {
        Value term = (Value) expr.getSub().accept(this);
        if (term.getType() instanceof TermType) {
            //TODO better and new
            TermValue data = (TermValue) term.getData();
            Pattern pattern = Pattern.compile("\\?[a-zA-Z_]+");
            String termstr = data.getTermRepr();
            Matcher m = pattern.matcher(termstr);
            StringBuffer newTerm = new StringBuffer();
            while (m.find()) {
                String name = m.group().substring(1); // remove trailing '?'
                Expression t = expr.getSubstitution().get(m.group());

                //either evalute the substitent or find ?X in the
                String newVal = "";
                if (t != null)
                    newVal = ((Value) t.accept(this)).getData().toString();
                else
                    // newVal = state.getValue(new Variable(name)).getData().toString();
                    m.appendReplacement(newTerm, newVal);
            }
            m.appendTail(newTerm);
            return new Value<>(TypeFacade.ANY_TERM, new TermValue(newTerm.toString()));
        } else {
            throw new IllegalStateException("Try to apply substitute on a non-term value.");
        }
    }

}
