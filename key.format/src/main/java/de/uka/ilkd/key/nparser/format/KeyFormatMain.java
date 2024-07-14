/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import picocli.CommandLine;
import picocli.CommandLine.Command;

public class KeyFormatMain {
    private static void formatSingleFile(Path input, Path output) throws IOException {
        var content = Files.readString(input);
        var formatted = format(content);

        if (formatted == null) {
            System.err.println("Failed to format " + input);
            return;
        }

        if (!formatted.equals(format(formatted))) {
            System.err.println("Formatter is not convergent on " + input);
        }

        var noWhitespaceContent = content.replaceAll("\\s+", "");
        var noWhitespaceFormatted = formatted.replaceAll("\\s+", "");
        if (!noWhitespaceContent.equals(noWhitespaceFormatted)) {
            System.err.println("File changed: " + input);
        }

        Files.writeString(output, formatted);
    }

    private static void formatSingleFileInSameDir(Path input) throws IOException {
        var fileName = input.getFileName().toString();
        if (!fileName.endsWith(".key")) {
            System.err.println("Ignoring non key file " + input);
            return;
        }
        var stem = fileName.substring(0, fileName.length() - 4);
        var output = input.resolveSibling(stem + ".format.key");
        formatSingleFile(input, output);
    }

    private static void formatSingleFileTo(Path input, Path outputDir) throws IOException {
        var output = outputDir.resolve(input.getFileName());
        formatSingleFile(input, output);
    }

    private static void formatDirectoryTest(Path dir) throws IOException {
        Path outDir = dir.getParent().resolve("output");
        // noinspection ResultOfMethodCallIgnored
        outDir.toFile().mkdirs();
        try (Stream<Path> s = Files.list(dir)) {
            s.forEach(p -> {
                var file = dir.resolve(p.getFileName());
                try {
                    var name = file.getFileName().toString();
                    if (name.endsWith(".format.format.key")) {
                        // noinspection ResultOfMethodCallIgnored
                        file.toFile().delete();
                        return;
                    }
                    formatSingleFileInSameDir(file);
                    if (!name.endsWith(".format.key")) {
                        formatSingleFileTo(file, outDir);
                    }
                } catch (Exception e) {
                    System.err.println("Exception while processing " + file);
                    throw new RuntimeException(e);
                }
            });
        }
    }

    private static boolean formatOrCheckInPlace(Path file, boolean format) {
        try {
            var content = Files.readString(file);
            var formatted = format(content);
            if (formatted == null) {
                System.err.println("Failed to format " + file);
                return false;
            }

            var differs = !content.equals(formatted);
            if (differs) {
                if (format) {
                    Files.writeString(file, formatted);
                } else {
                    System.err.println(file + " is not formatted correctly");
                    return false;
                }
            }
        } catch (Exception e) {
            System.err.println("Exception while processing " + file);
            e.printStackTrace();
            return false;
        }
        return true;
    }

    private static List<Path> expandPath(Path path) {
        if (!Files.exists(path)) {
            System.err.println("Input path does not exist");
            throw new IllegalStateException();
        }

        if (file.isDirectory()) {
            try (Stream<Path> s = Files.walk(path)) {
                return s.collect(Collectors.toList());
            }
        } else {
            return Collections.singletonList(path);
        }
    }

    @Command("format")
    private static class Format implements Callable<Integer> {
        @Argument(required = true)
        Path path;

        @Override
        public Integer call() throws Exception {
            var valid = expandPath(path).stream().map(it -> formatOrCheckInPlace(f, true)).all();
            return valid ? 0 : 1;
        }
    }

    @Command("check")
    private static class Format implements Callable<Integer> {
        @Argument(required = true)
        Path path;

        @Override
        public Integer call() throws Exception {
            var valid = expandPath(path).stream().map(it -> formatOrCheckInPlace(f, false)).all();
            return valid ? 0 : 1;
        }
    }

    public static void main(String[] args) throws IOException {
        int exitCode = new CommandLine(new Format(), new Check()).execute(args);
        System.exit(exitCode);
    }
}
