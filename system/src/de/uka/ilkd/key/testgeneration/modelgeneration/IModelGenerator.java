package de.uka.ilkd.key.testgeneration.modelgeneration;

import java.text.ParseException;
import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

/**
 * 
 * The Model Generator is used in order to turn the path condition for a given
 * {@link IExecutionNode} into a set of concrete values for the purpose of 
 * instantiating a test fixture.<p>
 * 
 * It works in the following way:<p>
 * 
 * The Model Generator can take either the {@code node} itself, or a 
 * {@link Term} representing the path condition for such a {@code node}.
 * 
 * The models created by a model generator must return a triplet for each generated
 * program element, containing the name, type and value of that element. Such triplets
 * must be instances of the {@link IModelContainer} interface, which is a simple
 * container type.
 * 
 * @author christopher
 * @see SolverLauncher
 * @see IExecutionNode
 * @see SymbolicExecutionEnvironment
 */
public interface IModelGenerator {
    
    public HashMap<String, IModelContainer> generateModel(IExecutionNode node) throws Exception;
    
    public interface IModelContainer {
        
        public enum Type {

            INTEGER,
            BOOLEAN,
            FLOAT,
            DOUBLE,
            LONG,
            BYTE,
            OBJECT;
        }
        
        public String getName();
        public void setName(String name);
        
        public Type getType();
        public void setType(Type type);
        
        public Object getValue();
        public void setValue(Object value);
    }

}
