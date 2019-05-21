package org.key_project.editor;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.MultipleCDockableFactory;
import bibliothek.gui.dock.common.MultipleCDockableLayout;
import bibliothek.util.xml.XElement;
import de.uka.ilkd.key.gui.MainWindow;
import lombok.Data;
import lombok.val;
import org.fife.ui.rsyntaxtextarea.Theme;
import org.key_project.editor.keyfile.KeyEditorFactory;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class EditorFacade {
    private static Theme EDITOR_THEME;
    private static List<EditorFactory> factories = new ArrayList<>();
    private static EditorDockableFactory editorDockableFactory = new EditorDockableFactory();

    static {
        factories.add(new KeyEditorFactory());
        factories.add(new FallbackEditorFactory());
    }

    public static MultipleCDockableFactory<?, ?> getEditorDockableFactory() {
        return editorDockableFactory;
    }

    public static void register(EditorFactory factory) {
        factories.add(0, factory);
    }

    public static Editor open(String mimeType) {
        Editor e;
        for (EditorFactory it : factories) {
            if ((e = it.open(mimeType)) != null)
                return e;
        }
        return null;
    }

    public static Editor open(Path path) {
        Editor e;
        try {
            for (EditorFactory it : factories) {
                if ((e = it.open(path)) != null)
                    return e;
            }
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        return null;
    }

    public static void addEditor(Editor editor, MainWindow mainWindow) {
        DefaultMultipleCDockable dockable = editor.getDockable();
        mainWindow.getDockControl().addDockable(dockable);
        dockable.setLocation(CLocation.base().normalWest(.2));
        dockable.setVisible(true);
    }

    public static List<EditorFactory> getEditorFactories() {
        return factories;
    }

    Theme getEditorTheme() {
        if (EDITOR_THEME == null) {
            InputStream themeRes = EditorFacade
                    .class.getResourceAsStream("org/fife/ui/rsyntaxtextarea/themes/eclipse.xml");
            if (null != themeRes) {
                try {
                    EDITOR_THEME = Theme.load(themeRes);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
        return EDITOR_THEME;
    }

    @Data
    public static class EditorDockableData implements MultipleCDockableLayout {
        private String path, textContent, mimeType;

        @Override
        public void writeStream(DataOutputStream dataOutputStream) throws IOException {
            dataOutputStream.writeUTF(path);
            dataOutputStream.writeUTF(textContent);
            dataOutputStream.writeUTF(mimeType);
        }

        @Override
        public void readStream(DataInputStream dataInputStream) throws IOException {
            path = dataInputStream.readUTF();
            textContent = dataInputStream.readUTF();
            mimeType = dataInputStream.readUTF();
        }

        @Override
        public void writeXML(XElement xElement) {
            xElement.getAttribute("PATH").setString(path);
            xElement.getAttribute("TEXT_CONTENT").setString(textContent);
            xElement.addString("MIMETYPE", mimeType);
        }

        @Override
        public void readXML(XElement xElement) {
            path = xElement.getAttribute("PATH").getString();
            textContent = xElement.getAttribute("TEXT_CONTENT").getString();
            mimeType = xElement.getString("MIMETYPE");
        }
    }

    public static class EditorDockableFactory
            implements MultipleCDockableFactory<DefaultMultipleCDockable, EditorDockableData> {
        @Override
        public EditorDockableData write(DefaultMultipleCDockable defaultMultipleCDockable) {
            val editor = (Editor) defaultMultipleCDockable.getContentPane();
            EditorDockableData dockableData = create();
            dockableData.path = editor.getPath().toString();
            dockableData.textContent = editor.getText();
            dockableData.mimeType = editor.getMimeType();
            return dockableData;
        }

        @Override
        public DefaultMultipleCDockable read(EditorDockableData editorDockableData) {
            if (editorDockableData.path != null && !editorDockableData.path.isBlank())
                return open(Paths.get(editorDockableData.path)).getDockable();
            else {
                val e = open(editorDockableData.mimeType);
                e.setText(editorDockableData.textContent);
                return e.getDockable();
            }
        }

        @Override
        public boolean match(DefaultMultipleCDockable defaultMultipleCDockable,
                             EditorDockableData editorDockableData) {
            return editorDockableData.equals(write(defaultMultipleCDockable));
            /*return Objects.equals(editor.getPath().toString(), editorDockableData.path)
                    && Objects.equals(editor.getMimeType(), editorDockableData.mimeType)
                    && Objects.equals(editor.getText(), editorDockableData.textContent);
                   */
        }

        @Override
        public EditorDockableData create() {
            return new EditorDockableData();
        }
    }

    static class FallbackEditorFactory implements EditorFactory {
        @Override
        public String getName() {
            return "text/plain";
        }

        @Override
        public Editor open(Path path) throws IOException {
            val e = open();
            e.setText(Files.readString(path));
            e.setDirty(false);
            e.setPath(path);
            return e;
        }

        @Override
        public Editor open(String mimeType) {
            return open();
        }

        @Override
        public Editor open() {
            val e = new Editor();
            e.setMimeType("text/plain");
            return e;
        }
    }
}
