package org.key_project.slicing;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.event.MouseWheelEvent;
import java.awt.event.MouseWheelListener;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;

public class PanZoomImageView extends JComponent implements MouseListener, MouseMotionListener, MouseWheelListener {
    private final transient BufferedImage image;
    private final AffineTransform at;
    private Timer timer;
    private long lastPaint = 0;
    private boolean quickRender = false;

    public PanZoomImageView(BufferedImage img, int width, int height) {
        this.image = img;

        int imageWidth = image.getWidth();
        int imageHeight = image.getHeight();
        double scale = 1.0;
        float scaleX = (float) width / imageWidth;
        float scaleY = (float) height / imageHeight;
        if (scaleX < 1.0 || scaleY < 1.0) {
            scale = Math.min(scaleX, scaleY);
        }
        var x = (width - scale * imageWidth) / 2;
        var y = (height - scale * imageHeight) / 2;
        at = AffineTransform.getScaleInstance(scale, scale);
        at.translate(x, y);

        this.timer = new Timer(150, e -> {
            if (quickRender && System.currentTimeMillis() - lastPaint > 100) {
                quickRender = false;
                repaint();
                this.timer.stop();
            }
        });
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);

        Graphics2D g2 = (Graphics2D) g;
        g2.setRenderingHint(RenderingHints.KEY_INTERPOLATION, quickRender ? RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR : RenderingHints.VALUE_INTERPOLATION_BICUBIC);
        g2.drawRenderedImage(image, at);
    }

    private final Point p = new Point();

    @Override
    public void mouseClicked(MouseEvent e) {

    }

    @Override
    public void mousePressed(MouseEvent e) {
        p.setLocation(e.getPoint());
    }

    @Override
    public void mouseReleased(MouseEvent e) {
    }

    @Override
    public void mouseEntered(MouseEvent e) {

    }

    @Override
    public void mouseExited(MouseEvent e) {
    }

    @Override
    public void mouseDragged(MouseEvent e) {
        var deltaX = e.getX() - p.getX();
        var deltaY = e.getY() - p.getY();
        var newAt = AffineTransform.getTranslateInstance(deltaX, deltaY);
        at.preConcatenate(newAt);
        p.setLocation(e.getPoint());
        quickRender = true;
        RepaintManager.currentManager(this).markCompletelyDirty(this);
        lastPaint = System.currentTimeMillis();
        this.timer.start();
    }

    @Override
    public void mouseMoved(MouseEvent e) {
    }

    @Override
    public void mouseWheelMoved(MouseWheelEvent e) {
        var scale = e.getWheelRotation() < 0 ? 1.1 : 0.9;
        var mod = AffineTransform.getTranslateInstance(e.getX(), e.getY());
        mod.scale(scale, scale);
        mod.translate(-e.getX(), -e.getY());
        at.preConcatenate(mod);
        quickRender = true;
        RepaintManager.currentManager(this).markCompletelyDirty(this);
        lastPaint = System.currentTimeMillis();
        this.timer.start();
    }
}