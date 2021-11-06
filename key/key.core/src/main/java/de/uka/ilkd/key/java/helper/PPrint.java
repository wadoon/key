package de.uka.ilkd.key.java.helper;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.google.common.base.Strings;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (11/6/21)
 */
public class PPrint {
    private boolean plain = true;
    private boolean pprint = true;
    private boolean ast = true;

    public static void main(String[] args) {
        PPrint p = new PPrint();
        for (String arg : args) {
            switch (arg) {
                case "--help":
                    return;
                case "--key":
                    p.plain = false;
                    return;
                case "-P":
                    p.pprint = false;
                    return;
                case "-p":
                    p.pprint = true;
                    return;
                case "-A":
                    p.ast = false;
                    return;
                case "-a":
                    p.ast = false;
                    return;
                default:
                    try {
                        p.process(new File(arg));
                    } catch (FileNotFoundException e) {
                        e.printStackTrace();
                    }
            }
        }

    }

    private void process(File file) throws FileNotFoundException {
        ParseResult<CompilationUnit> result;
        var jpb = new JavaParser();
        var startTime = System.nanoTime();
        result = jpb.parse(file);
        var stopTime = System.nanoTime();
        var durationNano = stopTime - startTime;

        System.out.format("// File: %s%n", file);
        System.out.format("// Parsing took: %8f ms%n", durationNano / 1000.0 / 1000.0);
        if (result.isSuccessful()) {
            System.out.println("// Parsing was successful");
        } else {
            result.getProblems().forEach(it -> System.out.format("// %s %n", it));
        }


        if (result.getResult().isPresent()) {
            var r = result.getResult().get();

            if (!plain) {
                //KeY pipeline

            }


            if (pprint) {
                var c = new DefaultPrinterConfiguration();
                var v = new DefaultPrettyPrinter(c);
                var pp = v.print(r);
            }

            if (ast) {
                printNode(r, "[0]", 0);
            }
        }
    }

    private void printNode(Node n, String text, int indent) {
        System.out.format("%s: %s %n", text, n.getMetaModel().getTypeName());

        var metaModel = n.getMetaModel();
        var allPropertyMetaModels = metaModel.getAllPropertyMetaModels();
        var attributes = allPropertyMetaModels.stream().filter(PropertyMetaModel::isAttribute)
                .filter(PropertyMetaModel::isSingular)
                .collect(Collectors.toList());

        var subNodes = allPropertyMetaModels.stream().filter(PropertyMetaModel::isNode)
                .filter(PropertyMetaModel::isSingular)
                .collect(Collectors.toList());
        var subLists = allPropertyMetaModels.stream().filter(PropertyMetaModel::isNodeList)
                .collect(Collectors.toList());

        for (var attributeMetaModel : attributes) {
            System.out.format(
                    "%s%s: %s = %s",
                    Strings.repeat("\t", indent),
                    attributeMetaModel.getName(),
                    attributeMetaModel.getTypeName(),
                    attributeMetaModel.getValue(n).toString()
            );
        }

        for (var subNodeMetaModel : subNodes) {
            var value = subNodeMetaModel.getValue(n);
            if (value != null) {
                printNode((Node) value, subNodeMetaModel.getName(), indent + 1);
            }
        }

        for (var subListMetaModel : subLists) {
            var subList = (NodeList<?>) subListMetaModel.getValue(n);
            if (subList != null && !subList.isEmpty()) {
                var listName = subListMetaModel.getName();
                System.out.format(
                        "%s%s: %s",
                        Strings.repeat("\t", indent),
                        listName,
                        subListMetaModel.getTypeName());

                for (int i = 0; i < subList.size(); i++) {
                    printNode(subList.get(i), "[" + i + "]", indent + 1);
                }
            }
        }
    }
}