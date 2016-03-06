package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.logic.op.SchemaVariable;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * Model for taclet instantiations. 
 * @author Victor Schuemmer
 */
public class TacletInstantiationRowModel {
    private final ObjectProperty<SchemaVariable> variable;
    private final StringProperty instantiation;
    private final IntegerProperty rowNumber;
    private boolean editable;
    
    /**
     * The constructor.
     * @param variable the variable
     * @param instantiation the instantiation
     * @param rowNumber the number of the row
     * @param editable if the instantiation should be editable
     */
    public TacletInstantiationRowModel(SchemaVariable variable, String instantiation, int rowNumber, boolean editable) {
        this.variable = new SimpleObjectProperty<SchemaVariable>(variable);
        this.instantiation = new SimpleStringProperty(instantiation != null ? instantiation : "");
        this.rowNumber = new SimpleIntegerProperty(rowNumber);
        this.editable = editable;
    }
    
    public SchemaVariable getVariable() {
        return variable.get();
    }
    
    public ObjectProperty<SchemaVariable> variableProperty() {
        return variable;
    }
    
    public void setVariable(SchemaVariable variable) {
        this.variable.set(variable);
    }
    
    public String getInstantiation() {
        return instantiation.get();
    }
    
    public StringProperty instantiationProperty() {
        return instantiation;
    }
    
    public void setInstantiation(String instantiation) {
        this.instantiation.set(instantiation != null ? instantiation : "");
    }

    public int getRowNumber() {
        return rowNumber.get();
    }
    
    public IntegerProperty rowNumberProperty() {
        return rowNumber;
    }
    
    public void setRowNumber(int rowNumber) {
        this.rowNumber.set(rowNumber);
    }
    
    public boolean isEditable() {
        return editable;
    }
    
    public void setEditable(boolean editable) {
        this.editable = editable;
    }
}
