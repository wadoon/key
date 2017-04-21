package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ArgumentsLifter {
    private static final Map<Class, Type> TYPE_MAP = new HashMap<>();

    public static List<ProofScriptArgument> inferScriptArguments(Class clazz) {
        List<ProofScriptArgument> args = new ArrayList<>();
        for (Field field : clazz.getFields()) {
            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                args.add(lift(option, field));
            }

            Flag flag = field.getDeclaredAnnotation(Flag.class);
            if (flag != null) {
                args.add(lift(flag, field));
            }
        }
        return args;
    }

    private static ProofScriptArgument lift(Option option, Field field) {
        ProofScriptArgument arg = new ProofScriptArgument();
        arg.setName(option.value());
        arg.setRequired(option.required());
        arg.setField(field);
        arg.setType(TYPE_MAP.get(field.getType()));
        return arg;
    }

    private static ProofScriptArgument lift(Flag flag, Field field) {
        return null;
    }
}