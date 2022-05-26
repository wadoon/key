package org.key_project.slicing.ui;

import javax.imageio.ImageIO;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;

/**
 * Dialog that displays a rendering of the dependency graph.
 * Requires an installation of graphviz on the system.
 *
 * @author Arne Keller
 */
public class PreviewDialog extends JDialog {
    public PreviewDialog(Window window, String dot) {
        super(window, "Preview");
        setLayout(new BorderLayout());
        var label = new JLabel("Running dot...");
        label.setBorder(new EmptyBorder(10, 10, 10, 10));
        getContentPane().add(label, BorderLayout.NORTH);

        new DotExecutor(dot, window, this).execute();

        pack();
        setLocationRelativeTo(window);
        setVisible(true);
    }

    private static class DotExecutor extends SwingWorker<Void, Void> {
        /**
         * Execution error.
         */
        private String error;
        /**
         * The rendered graph.
         */
        private BufferedImage img;
        /**
         * Graph to be rendered (dot format).
         */
        private final String dot;
        /**
         * The preview dialog.
         */
        private final PreviewDialog dialog;
        /**
         * The main window (used to set the relative position of the dialog).
         */
        private final Window window;

        public DotExecutor(String dot, Window window, PreviewDialog dialog) {
            this.dot = dot;
            this.window = window;
            this.dialog = dialog;
        }

        @Override
        protected Void doInBackground() {
            try {
                var process = new ProcessBuilder("dot", "-Tpng").start();
                var stdin = process.getOutputStream();
                stdin.write(dot.getBytes(StandardCharsets.UTF_8));
                stdin.close();
                var outStream = process.getInputStream();
                var errStream = process.getErrorStream();
                var output = new ByteArrayOutputStream();
                var stderr = new ByteArrayOutputStream();
                byte[] buffer = new byte[65536];
                while (process.isAlive()) {
                    if (outStream.available() > 0) {
                        int res = outStream.read(buffer);
                        if (res > 0) {
                            output.write(buffer, 0, res);
                        }
                    }
                    if (errStream.available() > 0) {
                        int res2 = errStream.read(buffer);
                        if (res2 > 0) {
                            stderr.write(buffer, 0, res2);
                        }
                    }
                }
                if (process.exitValue() != 0) {
                    error = stderr.toString();
                } else {
                    img = ImageIO.read(new ByteArrayInputStream(output.toByteArray()));
                    //ImageIO.write(img, "PNG", new File("/tmp/x2.png"));
                }
            } catch (IOException e) {
                error = e.getMessage();
            }
            return null;
        }

        @Override
        protected void done() {
            super.done();
            if (img != null) {
                dialog.getContentPane().removeAll();
                var pziv = new PanZoomImageView(img, 800, 600);
                pziv.setPreferredSize(new Dimension(800, 600));
                dialog.getContentPane().add(pziv, BorderLayout.CENTER);
                pziv.addMouseListener(pziv);
                pziv.addMouseMotionListener(pziv);
                pziv.addMouseWheelListener(pziv);
                dialog.pack();
                dialog.setLocationRelativeTo(window);
            } else {
                var label = new JLabel(error);
                label.setBorder(new EmptyBorder(0, 10, 10, 10));
                dialog.getContentPane().add(label, BorderLayout.SOUTH);
                dialog.pack();
            }
        }
    }
}
