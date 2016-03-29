package de.uka.ilkd.key.nui.view;

import javafx.application.Platform;
import javafx.beans.binding.Bindings;
import javafx.scene.control.Cell;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TextArea;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.util.Callback;
import javafx.util.StringConverter;
import javafx.util.converter.DefaultStringConverter;

/**
 * Custom TableCell which supports multiline editing and committing on focus
 * loss.
 * 
 * @author Victor Schuemmer
 * @version 1.0
 */
public class TextAreaTableCell<S, T> extends TableCell<S, T> {

    private TextArea textArea;
    private StringConverter<T> converter;

    /**
     * @return factory method to create a TextAreaTableCell<S, String>, where S
     *         is the underlying model of the table.
     */
    public static <S> Callback<TableColumn<S, String>, TableCell<S, String>> forTableColumn() {
        return forTableColumn(new DefaultStringConverter());
    }

    /**
     * @return factory method to create a TextAreaTableCell<S, T>, where S
     *         is the underlying model of the table.
     */
    public static <S, T> Callback<TableColumn<S, T>, TableCell<S, T>> forTableColumn(
            final StringConverter<T> converter) {
        return list -> new TextAreaTableCell<>(converter);
    }

    private static <T> String getItemText(Cell<T> cell,
            StringConverter<T> converter) {
        return converter == null
                ? cell.getItem() == null ? "" : cell.getItem().toString()
                : converter.toString(cell.getItem());
    }

    private static <T> TextArea createTextArea(final Cell<T> cell,
            final StringConverter<T> converter) {

        TextArea textArea = new TextArea(getItemText(cell, converter));

        Tooltip t = new Tooltip(
                "Press Shift+Enter to apply changes or Esc to cancel.");
        Tooltip.install(textArea, t);

        textArea.setOnKeyReleased(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                cell.cancelEdit();
                e.consume();
            }
            else if (e.getCode() == KeyCode.ENTER && e.isShiftDown()) {
                cell.commitEdit(
                        converter.fromString(textArea.getText().trim()));
                e.consume();
            }
        });
        textArea.focusedProperty().addListener((observable, oldVal, newVal) -> {
            if (!newVal)
                cell.commitEdit(
                        converter.fromString(textArea.getText().trim()));
        });

        textArea.prefRowCountProperty()
                .bind(Bindings.size(textArea.getParagraphs()));
        return textArea;
    }

    /**
     * Constructs a TextAreaTableCell with the given {@link StringConverter<T>}
     * 
     * @param converter
     *            StringConverter to convert a string from the table to the
     *            model backing the table.
     */
    public TextAreaTableCell(StringConverter<T> converter) {
        this.getStyleClass().add("text-area-table-cell");
        this.converter = converter;
    }

    private void startEdit(final Cell<T> cell,
            final StringConverter<T> converter) {
        if (textArea == null)
            textArea = createTextArea(this, converter);
        textArea.setText(getItemText(cell, converter));

        cell.setText(null);
        cell.setGraphic(textArea);

        textArea.selectAll();
        textArea.requestFocus();
    }

    private static <T> void cancelEdit(Cell<T> cell,
            final StringConverter<T> converter) {
        cell.setText(getItemText(cell, converter));
        cell.setGraphic(null);
    }

    private void updateItem(final Cell<T> cell,
            final StringConverter<T> converter) {

        if (cell.isEmpty()) {
            cell.setText(null);
            cell.setGraphic(null);

        }
        else {
            if (cell.isEditing()) {
                textArea.setText(getItemText(cell, converter));

                cell.setText(null);
                cell.setGraphic(textArea);
            }
            else {
                cell.setText(getItemText(cell, converter));
                cell.setGraphic(null);
            }
        }
    }

    @Override
    public void startEdit() {
        if (!isEditable() || !getTableView().isEditable()
                || !getTableColumn().isEditable()) {
            return;
        }

        super.startEdit();

        if (isEditing()) {
            startEdit(this, converter);
            Platform.runLater(() -> textArea.requestFocus());
        }
    }

    @Override
    public void cancelEdit() {
        super.cancelEdit();
        cancelEdit(this, converter);
    }

    @Override
    public void updateItem(T item, boolean empty) {
        super.updateItem(item, empty);
        updateItem(this, converter);
    }
}
