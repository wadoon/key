package de.uka.ilkd.key.testgeneration.backend.templates;

import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupDir;

public class TemplateTest {

    public static void main(String[] args) {

        STGroup group = new STGroupDir(
                "system/src/de/uka/ilkd/key/testgeneration/backend/templates");
        ST st = group.getInstanceOf("decl");
        st.add("type", "int");
        st.add("type", "bool");
        st.add("type", "float");
        st.add("name", "x");
        // st.add("value", 0);
        String result = st.render(); // yields "int x = 0;"
        System.out.println(result);

    }
}
