package de.uka.ilkd.key.testgeneration.parser.z3parser.api;

import java.io.ByteArrayInputStream;
import java.text.ParseException;
import java.util.HashMap;
import de.uka.ilkd.key.testgeneration.parser.z3parser.api.Z3Visitor.ValueContainer;
import de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Yylex;
import de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.parser;
import de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Mod;
import de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Modl;

public class Z3ModelParser {

    public static HashMap<String, ValueContainer> parseModel(Mod model) {

        HashMap<String, ValueContainer> parsedModel =
                new HashMap<String, ValueContainer>();
        model.accept(Z3Visitor.getInstance(), parsedModel);

        return parsedModel;
    }

    public static HashMap<String, ValueContainer> parseModel(String model)
            throws ParseException {

        Yylex lexer = null;
        parser parser = null;

        lexer = new Yylex(new ByteArrayInputStream(model.getBytes()));

        parser = new parser(lexer);
        Modl modelTree;

        try {
            modelTree = parser.pModel();

        }
        catch (Exception e) {

            throw new ParseException(e.getMessage(), -1);
        }

        HashMap<String, ValueContainer> parsedModel =
                new HashMap<String, ValueContainer>();
        modelTree.accept(Z3Visitor.getInstance(), parsedModel);

        return parsedModel;
    }

}
