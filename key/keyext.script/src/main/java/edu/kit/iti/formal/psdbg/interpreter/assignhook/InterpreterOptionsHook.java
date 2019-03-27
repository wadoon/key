package edu.kit.iti.formal.psdbg.interpreter.assignhook;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import lombok.Getter;
import lombok.Setter;

import java.math.BigInteger;

public class InterpreterOptionsHook<T> extends DefaultAssignmentHook<T> {
    @Getter
    @Setter
    private Interpreter<T> interpreter;

    public InterpreterOptionsHook(Interpreter<T> interpreter) {
        this.interpreter = interpreter;

        register("__MAX_ITERATIONS_REPEAT",
                "Sets the the upper limit for iterations in repeat loops. Default value is really high.",
                (T data, Value<BigInteger> v) -> {
                    interpreter.setMaxIterationsRepeat(v.getData().intValue());
                    return true;
                },
                (T data) -> Value.from(interpreter.getMaxIterationsRepeat())
        );


        register("__STRICT_MODE",
                        "Defines if the interpreter is in strict or relax mode. \n\n" +
                        "In strict mode the interpreter throws an exception in following cases:\n\n" +
                        "* access to undeclared or unassigned variable\n" +
                        "* application of non-applicable rule\n\n" +
                        "In non-strict mode these errors are ignored&mdash;a warning is given on the console.",
                (T data, Value<Boolean> v) -> {
                    interpreter.setStrictMode(v.getData());
                    return true;
                },
                (T data) -> Value.from(interpreter.isStrictMode())
        );
    }
}
