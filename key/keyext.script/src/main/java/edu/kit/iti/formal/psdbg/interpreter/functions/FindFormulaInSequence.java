package edu.kit.iti.formal.psdbg.interpreter.functions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import edu.kit.iti.formal.psdbg.interpreter.Evaluator;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.InterpreterRuntimeException;
import edu.kit.iti.formal.psdbg.interpreter.matcher.KeyMatcherFacade;
import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.parser.ast.Expression;
import edu.kit.iti.formal.psdbg.parser.ast.FunctionCall;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.function.ScriptFunction;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.Optional;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * <h3>Examples</h3>
 * <code><pre>
 *     * find(`f(?X)`) => f(x)
 *     * find(``) =>
 * </pre></code>
 *
 * @author Alexander Weigl
 * @version 1 (10.11.17)
 * @version 2 (28.08.19)
 */
public class FindFormulaInSequence implements ScriptFunction {
    @NotNull
    @Override
    public String getName() {
        return "ffind";
    }

    @Override
    public @NotNull String getDocumentation() {
        return "ffind -- Find formula in sequent.\n\n" +
                "Synopsis:\tffind(a : STRING)\n" +
                "         \tffind(a : TERM)\n" +
                "\n" +
                "Description:\n\n" +
                "Find a formula";
    }

    @NotNull
    @Override
    public Type getType(List<Type> types) throws NotWelldefinedException {
        if (types.size() != 1)
            throw new NotWelldefinedException("Called with wrong arity.", null);
        if (types.get(0) != SimpleType.PATTERN && types.get(0) != SimpleType.STRING)
            throw new NotWelldefinedException("Wrong parameter type for " + getName(), null);
        return new TermType();
    }

    @NotNull
    public <T> Value eval(Evaluator<T> val, FunctionCall call)
            throws IllegalArgumentException {
        Evaluator<KeyData> e = (Evaluator<KeyData>) val;
        GoalNode<KeyData> data = e.getGoal();
        Goal goal = data.getData().getGoal();

        try {
            Expression expr = call.getArguments().get(0);
            Value pattern = e.eval(expr);
            Stream<SequentFormula> formulas = Stream.concat(
                    goal.sequent().antecedent().stream(),
                    goal.sequent().succedent().stream());

            if (TypeFacade.isTerm(pattern.getType())) {
                Services services = data.getData().getProof().getServices();
                Optional<Term> seq = formulas
                        .map(SequentFormula::formula)
                        .filter(it -> {
                            try {
                                return KeyMatcherFacade
                                        .matchesTerm(services, pattern.getData().toString(), it);
                            } catch (ParserException ex) {
                                ex.printStackTrace();
                                return false;
                            }
                        })
                        .findAny();
                Term formulae = seq.orElseThrow(() -> new InterpreterRuntimeException("Could not find a suitable match.", call));
                return new Value<>(new TermType(),
                        LogicPrinter.quickPrintTerm(formulae, services));
            } else if (pattern.getType() == SimpleType.STRING) {
                Pattern regex = Pattern.compile((String) pattern.getData());
                Services services = data.getData().getProof().getServices();
                Optional<String> seq = formulas
                        .map(it -> LogicPrinter.quickPrintTerm(it.formula(), services))
                        .filter(it -> regex.matcher(it).matches())
                        .findAny();
                String formulae = seq.orElseThrow(() -> new InterpreterRuntimeException("Could not find a suitable match.", call));
                return new Value<>(new TermType(), formulae);
            } else {
                throw new IllegalArgumentException("Matching only possible on terms.");
            }

        } catch (ClassCastException exc) {
            throw new IllegalStateException("Excepted a match expression as first argument found: " + call.getArguments().get(0),
                    exc);
        }
    }
}
