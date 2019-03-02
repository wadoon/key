package edu.key_project.script.ui;

import lombok.NonNull;

import java.util.Arrays;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (02.03.19)
 */
public class ScriptUtils {
    public static boolean isCommented(@NonNull String text) {
        text = text.trim();
        String[] lines = text.split("\n");
        return Arrays.stream(lines).allMatch(l -> l.trim().startsWith("//"));
    }

    public static String removeComments(@NonNull String text) {
        Pattern leadingComment = Pattern.compile("^//\\s?", Pattern.MULTILINE);
        return leadingComment.matcher(text).replaceAll("");
    }

    public static String comment(String text) {
        String[] lines = text.split("\n");
        return Arrays.stream(lines).map(s -> "// " + s).collect(Collectors.joining("\n"));
    }
}
