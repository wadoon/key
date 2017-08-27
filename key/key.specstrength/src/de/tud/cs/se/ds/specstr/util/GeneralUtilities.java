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

package de.tud.cs.se.ds.specstr.util;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import org.apache.logging.log4j.Logger;

/**
 * Miscellaneous utilities container class.
 *
 * @author Dominic Steinhoefel
 */
public final class GeneralUtilities {

    private GeneralUtilities() {
        // Hidden constructor -- it's a utility class.
    }

    /**
     * printf-style formats the given {@link String} with the given parameter
     * {@link Object}s. The syntax of {@link Formatter} applies.
     *
     * @param s
     *            The format {@link String}.
     * @param args
     *            The argument {@link Object}s to insert into the format
     *            {@link String}.
     * @return The formatted {@link String}.
     * @see Formatter
     */
    public static String format(String s, Object... args) {
        StringBuilder sb = new StringBuilder();

        Formatter formatter = new Formatter(sb, Locale.US);
        formatter.format(s, args);
        formatter.close();

        return sb.toString();
    }

    /**
     * Trims s and replaces all consequitive whitespace characters inside by
     * only one space.
     *
     * @param s
     *            The {@link String} to clean.
     * @return A cleaned-up representation of s, no whitespace at beginning and
     *         end, and at most one whitespace (a space) inside.
     */
    public static String cleanWhitespace(String s) {
        return s.trim().replaceAll("(\\s)+", " ");
    }

    /**
     * Tries to parse a {@link String} to an {@link Integer}; returns an
     * {@link Optional} containing the {@link Integer} in case of success or an
     * empty {@link Optional} otherwise.
     *
     * @param s
     *            The {@link String} to parse.
     * @return An {@link Optional} containing the {@link Integer} in case of
     *         success or an empty {@link Optional} otherwise.
     */
    public static Optional<Integer> tryParseInt(String s) {
        try {
            int result = Integer.parseInt(s);
            return Optional.of(result);
        }
        catch (NumberFormatException e) {
            return Optional.empty();
        }
    }

    /**
     * Logs an error messages and throws a {@link RuntimeException}; the message
     * for the logging and the exception is configured in printf-style.
     *
     * @see #format(String, Object...)
     * @param logger
     *            The {@link Logger} to which to send the message.
     * @param s
     *            The format {@link String}.
     * @param args
     *            The argument {@link Object}s to insert into the format
     *            {@link String}.
     * @throws RuntimeException
     *             Always throws a {@link RuntimeException}.
     */
    public static void logErrorAndThrowRTE(Logger logger, String s,
            Object... args) throws RuntimeException {
        final String msg = format(s, args);
        logger.error(msg);
        throw new RuntimeException(msg);
    }

    /**
     * Converts the given {@link Iterable} to a {@link Stream}.
     *
     * @param it
     *            The {@link Iterable} to convert to a {@link Stream}.
     * @return The {@link Stream} for the given {@link Iterable}.
     * @param <T>
     *            The type of {@link Iterable}.
     */
    public static <T> Stream<T> toStream(Iterable<T> it) {
        return StreamSupport.stream(it.spliterator(), false);
    }

    /**
     * Returns a merge function, suitable for use in
     * {@link Map#merge(Object, Object, BiFunction) Map.merge()} or
     * {@link #toMap(Function, Function, BinaryOperator) toMap()}, which always
     * throws {@code IllegalStateException}. This can be used to enforce the
     * assumption that the elements being collected are distinct.
     *
     * @param <T>
     *            the type of input arguments to the merge function
     * @return a merge function which always throw {@code IllegalStateException}
     * @see Collectors
     */
    private static <T> BinaryOperator<T> throwingMerger() {
        return (u, v) -> {
            throw new IllegalStateException(
                    String.format("Duplicate key %s", u));
        };
    }

    /**
     * Returns a {@link LinkedHashMap} as opposed to
     * {@link Collectors#toMap(Function, Function)} which will return a
     * {@link HashMap} with unpredictable iteration order.
     *
     * @param <T>
     *            the type of the input elements
     * @param <K>
     *            the output type of the key mapping function
     * @param <U>
     *            the output type of the value mapping function
     * @param keyMapper
     *            a mapping function to produce keys
     * @param valueMapper
     *            a mapping function to produce values
     * @return a {@code Collector} which collects elements into a
     *         {@code LinkedHashMap} whose keys and values are the result of
     *         applying mapping functions to the input elements
     */
    public static <T, K, U> Collector<T, ?, LinkedHashMap<K, U>> toLinkedHashMap(
            Function<? super T, ? extends K> keyMapper,
            Function<? super T, ? extends U> valueMapper) {
        return Collectors.toMap(keyMapper, valueMapper, throwingMerger(),
                LinkedHashMap::new);
    }

}
