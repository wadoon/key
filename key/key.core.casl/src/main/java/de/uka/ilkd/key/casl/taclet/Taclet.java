package de.uka.ilkd.key.casl.taclet;

import de.uka.ilkd.key.casl.main.Util;
import de.uka.ilkd.key.casl.transform.Transform;
import org.stringtemplate.v4.Interpreter;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;
import org.stringtemplate.v4.gui.STViz;
import org.stringtemplate.v4.misc.ObjectModelAdaptor;
import org.stringtemplate.v4.misc.STNoSuchPropertyException;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.RecordComponent;
import java.util.logging.Logger;

public final class Taclet {
    private static final Logger LOGGER = Util.getLogger(Taclet.class);

    private static final STGroup STG = new STGroupFile("org/stressinduktion/keycasl/taclet-stg/taclet.stg");
    static {
        STG.registerModelAdaptor(Record.class, new STRecordAdapter());
    }

    private static final class STRecordAdapter extends ObjectModelAdaptor<Record> {
        @Override
        public synchronized Object getProperty(Interpreter interp, ST self, Record model, Object property,
                                               String propertyName) throws STNoSuchPropertyException {
            RecordComponent[] recordComponents = model.getClass().getRecordComponents();
            for (var r : recordComponents) {
                if (propertyName.equals(r.getName())) {
                    try {
                        return r.getAccessor().invoke(model);
                    } catch (IllegalAccessException | InvocationTargetException e) {
                        throw new RuntimeException(e);
                    }
                }
            }

            return super.getProperty(interp, self, model, property, propertyName);
        }
    }

    public static String render(Transform.Taclet taclet) throws InterruptedException {
        return render(taclet, false);
    }

    public static String render(Transform.Taclet taclet, boolean inspect) throws InterruptedException {
        ST tacletTpl = STG.getInstanceOf("taclet");
        tacletTpl.add("sorts", taclet.sorts());
        tacletTpl.add("defaultValues", taclet.defaultValues());
        tacletTpl.add("functions", taclet.functions());
        tacletTpl.add("axioms", taclet.axioms());
        tacletTpl.add("inductions", taclet.induction());
        tacletTpl.add("splits", taclet.split());
        tacletTpl.add("problem", taclet.problem());
        tacletTpl.add("equalities", taclet.equalities());
        if (inspect) {
            STViz stViz = tacletTpl.inspect();
            stViz.waitForClose();
        }
        return tacletTpl.render();
    }
}
