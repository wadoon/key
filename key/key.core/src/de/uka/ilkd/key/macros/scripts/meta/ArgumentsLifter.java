package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public final class ArgumentsLifter {
    //private static final Map<Class, Type> TYPE_MAP = new HashMap<>();

    private ArgumentsLifter() {
    }

    public static <T> List<ProofScriptArgument<T>> inferScriptArguments(Class clazz, ProofScriptCommand<T> command) {
        List<ProofScriptArgument<T>> args = new ArrayList<>();
        for (Field field : clazz.getDeclaredFields()) {
            ProofScriptArgument<T> argument = new ProofScriptArgument<T>();
            argument.setCommand(command);
            boolean add = false;

            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                lift(argument, option, field);
                add = true;
            }

            Flag flag = field.getDeclaredAnnotation(Flag.class);
            if (flag != null) {
                lift(argument, flag, field);
                add = true;
            }

            Varargs vargs = field.getDeclaredAnnotation(Varargs.class);
            if (vargs != null) {
                lift(argument, vargs, field);
                add=true;
            }

            if (add) {
                args.add(argument);
            }
        }
        //
        args.forEach(a -> a.setCommand(command));
        return args;
    }

    private static ProofScriptArgument lift(ProofScriptArgument arg, Varargs vargs, Field field) {
        arg.setName(vargs.prefix());
        arg.setRequired(false);
        arg.setField(field);
        arg.setType(vargs.as());
        arg.setVariableArguments(true);
        arg.setDocumentation(DescriptionFacade.getDocumentation(arg));
        return arg;
    }

    private static ProofScriptArgument lift(ProofScriptArgument arg, Option option, Field field) {
        arg.setName(option.value());
        arg.setRequired(option.required());
        arg.setField(field);
        arg.setType(field.getType());
        arg.setDocumentation(DescriptionFacade.getDocumentation(arg));
        return arg;
    }

    private static ProofScriptArgument lift(ProofScriptArgument argument, Flag flag, Field field) {
        throw new IllegalStateException("not implemented");
    }
}