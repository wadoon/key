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
 * @version 1.0
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
     * @param editable true iff the instantiation should be editable
     */
    public TacletInstantiationRowModel(SchemaVariable variable, String instantiation, int rowNumber, boolean editable) {
        this.variable = new SimpleObjectProperty<SchemaVariable>(variable);
        this.instantiation = new SimpleStringProperty(instantiation != null ? instantiation : "");
        this.rowNumber = new SimpleIntegerProperty(rowNumber);
        this.editable = editable;
    }
    
    /**
     * @return the variable
     */
    public SchemaVariable getVariable() {
        return variable.get();
    }
    
    /**
     * @return the variable property
     */
    public ObjectProperty<SchemaVariable> variableProperty() {
        return variable;
    }
    
    /**
     * Sets the variable.
     * @param variable
     */
    public void setVariable(SchemaVariable variable) {
        this.variable.set(variable);
    }
    
    /**
     * @return the instantiation
     */
    public String getInstantiation() {
        return instantiation.get();
    }
    
    /**
     * @return the instantiation property
     */
    public StringProperty instantiationProperty() {
        return instantiation;
    }
    
    /**
     * Sets the instantiation.
     * @param instantiation
     */
    public void setInstantiation(String instantiation) {
        this.instantiation.set(instantiation != null ? instantiation : "");
    }

    /**
     * @return the number of this row
     */
    public int getRowNumber() {
        return rowNumber.get();
    }
    
    /**
     * @return the row number property
     */
    public IntegerProperty rowNumberProperty() {
        return rowNumber;
    }
    
    /**
     * Sets the number of this row.
     * @param rowNumber
     */
    public void setRowNumber(int rowNumber) {
        this.rowNumber.set(rowNumber);
    }
    
    /**
     * @return true iff the instantiation is allowed to be edited.
     */
    public boolean isEditable() {
        return editable;
    }
    
    /**
     * Sets if the instantiation is allowed to be edited.
     * @param editable
     */
    public void setEditable(boolean editable) {
        this.editable = editable;
    }
}
