package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.Taclet;
import org.key_project.util.collection.ImmutableList;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (11.09.17)
 */
public class GenDoc {
    private static final Set<String> FORBBIDEN = new TreeSet<>();

    static {
        FORBBIDEN.add("exit");
        FORBBIDEN.add("focus");
        FORBBIDEN.add("javascript");
        FORBBIDEN.add("leave");
        FORBBIDEN.add("let \n");
    }

    private static final File basedir = new File("..");
    private static final File propertiesFile = new File(basedir,
            "taclets.properties.xml");
    private static final File dummyFile = new File(".",
            "key.ui/examples/standard_key/prop_log/contraposition.key");
    private static final File websiteDoc = new File(basedir, "website/docs/");


    private static List<Taclet> getTaclets() throws ProblemLoaderException {
        System.out.println("Use dummy file: " + dummyFile.getAbsolutePath());
        KeYEnvironment<?> env = KeYApi.loadFromKeyFile(dummyFile).getLoadedProof().getEnv();
        ImmutableList<Taclet> a = env.getInitConfig().getTaclets();
        return a.stream().collect(Collectors.toList());
    }

    private static void writeProperties(File file, List<Taclet> taclets) {
        Properties documentation = new Properties();
        for (Taclet taclet : taclets) {
            System.out.println((taclet.displayName()));
            documentation.put(taclet.displayName(), taclet.toString());
        }
        // write properties file!
        propertiesFile.getParentFile().mkdirs();
        try (FileOutputStream stream = new FileOutputStream(file)) {
            documentation.storeToXML(stream,
                    String.format("Generated on: %s. Use gen", new Date()),
                    StandardCharsets.UTF_8);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void writeTacletDocumentation(PrintWriter stream, List<Taclet> taclets) {
        stream.write("# Taclets\n\n");
        for (Taclet t : taclets) {
            stream.format("%n%n## %s%n%n", t.displayName());
            stream.format("defined in %s", t.getOrigin());

            t.getIfFindVariables().forEach(it ->
                    stream.format("%n* Var %s", it)
            );

            //stream.write("```\n" + t + "\n```");
        }
    }

    private static void writeMacros(PrintWriter stream) {
        List<ProofMacro> macros = new ArrayList<>(KeYApi.getMacroApi().getMacros());
        macros.sort(Comparator.comparing(ProofMacro::getScriptCommandName));

        stream.write("# Macros\n\n");

        for (ProofMacro t : macros) {
            stream.format("%n%n## `%s` -- %s %n%n",
                    t.getScriptCommandName(), t.getName());
            stream.write(t.getCategory() + "\n\n");
            stream.write(t.getDescription() + "\n\n");
        }
    }

    private static String helpForCommand(ProofScriptCommand<?> c) {
        StringBuilder html = new StringBuilder();
        html.append("## ").append(c.getName());
        html.append("\n> Synopsis: `").append(c.getName());

        for (ProofScriptArgument<?> a : c.getArguments()) {
            html.append(' ');
            if (a.isFlag()) {
                html.append("[").append(a.getName()).append("]");
            } else {
                if (!a.isRequired())
                    html.append("[");

                if (a.getName().startsWith("#"))
                    html.append("<").append(a.getType().getSimpleName().toUpperCase()).append(">");
                else
                    html.append(a.getName()).append("=<").append(a.getType().getSimpleName().toUpperCase()).append(">");

                if (!a.isRequired())
                    html.append("]");
            }
        }
        html.append("`\n\n");

        html.append(c.getDocumentation().replaceAll("\n[ \t]*", "\n"));

        html.append("\n\n**Arguments:**\n");
        for (ProofScriptArgument<?> a : c.getArguments()) {
            html.append(
                    String.format("%n* `%s` :  *%s* ",
                            a.getName(), a.getType().getSimpleName().toUpperCase()));
            if (a.isRequired()) {
                html.append(" (**required**) ");
            }
            final var documentation = a.getDocumentation();
            html.append(documentation == null ? " not available" : documentation);
        }
        return html.toString();
    }


    private static void writeCommand(PrintWriter stream) {
        List<ProofScriptCommand<?>> commands = new ArrayList<>(KeYApi.getScriptCommandApi().getScriptCommands());
        stream.write("# Commands\n\n");
        stream.write("\n\nCovering the proof script commands of [KeY](http://key-project.org).\n\n");

        commands.sort(Comparator.comparing(ProofScriptCommand::getName));

        for (ProofScriptCommand<?> t : commands) {
            if (!FORBBIDEN.contains(t.getName()))
                stream.write(helpForCommand(t) + "\n\n");
        }
    }


    public static void main(String[] args) throws ProblemLoaderException, IOException {
        //writeProperties(propertiesFile, taclets);
        //writeTacletDocumentation(new File(websiteDoc, "taclets.md"), taclets);
        //writeMacros(new File(websiteDoc, "macros.md"));
        //writeCommand(new File(websiteDoc, "commands.md"));
        new GenDoc().writeAll(new File("scriptref.md"));
    }

    private void writeAll(File file) throws IOException, ProblemLoaderException {
        try (var stream = new PrintWriter(new FileWriter(file))) {
            writePreamble(stream);

            writeCommand(stream);
            writeMacros(stream);

            List<Taclet> taclets = getTaclets();
            taclets.sort(Comparator.comparing(Taclet::name));

            writeTacletDocumentation(stream, taclets);
        }
    }

    private void writePreamble(PrintWriter stream) {
        stream.println("# Reference for Proof Scripts");
        stream.format("*Generated on %s using `%s`* %n%n", new Date(), GenDoc.class.getName());

    }

}