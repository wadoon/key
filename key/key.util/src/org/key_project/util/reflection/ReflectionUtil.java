// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.util.reflection;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * TODO
 *
 * @author Dominic Steinhoefel
 */
public class ReflectionUtil {

    /**
     * TODO
     * 
     * @param resultClass
     * @param className
     * @param fieldName
     * @return
     */
    @SuppressWarnings("unchecked")
    public static <T> Optional<T> getField(Class<T> resultClass,
            String className, String fieldName) {
        try {
            final Class<?> c = Class.forName(className);
            return Optional.of((T) c.getField(fieldName).get(null));
        } catch (ClassNotFoundException | IllegalArgumentException
                | IllegalAccessException | NoSuchFieldException
                | SecurityException e) {
            return Optional.empty();
        }
    }

    /**
     * TODO
     * 
     * @param resultClass
     * @param obj
     * @param methodName
     * @param args
     * @return
     */
    @SuppressWarnings("unchecked")
    public static <T> Optional<T> callMethodOnObj(Class<T> resultClass,
            Object obj, String methodName, Object... args) {
        final Class<?> cls = obj.getClass();

        try {
            final Method m = cls.getMethod(methodName,
                    Arrays.stream(args).map(o -> o.getClass())
                            .collect(Collectors.toList())
                            .toArray(new Class[] {}));

            return Optional.of((T) m.invoke(obj, args));
        } catch (NoSuchMethodException | SecurityException
                | IllegalAccessException | IllegalArgumentException
                | InvocationTargetException e) {
            return Optional.empty();
        }
    }

}
