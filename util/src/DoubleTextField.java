package warwick.marsh.util;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.text.*;
import java.text.DecimalFormat;

/** Subclass of JTextField for range-checked floating point input. Supports
 * up and down arrows and left and right mouse buttons to increment 
 * and decrement the value.  Focus-follows-mouse behaviour.
 */

public class DoubleTextField extends JTextField {

    // For rounding decimal numbers
    private static final DecimalFormat form = new DecimalFormat();

    // The time between updates of the field when the mouse is held down, millisecs
    private static final int DELAY = 20;

    // The time between updates at the start to allow user to add one
    private static final int INITIAL_DELAY = 300;    

    private double  vmin;
    private double  vmax;
    private double  increment;
    private String name;
    private Color  normalColour;
    private Color  errorColour;

    private Timer  incrementTimer;

    /** Constructor with an intial value, a range and an indicator of whether the field
     * is enable.
     * @param value        the initial value to show in the field
     * @param vmin         the minimum possible value
     * @param vmax         the maximum possible value
     * @param increment    the step by which to increment when using the up/down arrows
     * @param name         name for the field for when reporting errors
     * @param enabled      is the field active or not
     * @param normalColour the normal colour for the field
     * @param errorColour  the colour when the field is in error
     * @param width        the field width
     */

    public DoubleTextField(double value, double vmin, double vmax, double increment, String name, boolean enabled, 
			  Color normalColour, Color errorColour, int width) {
	
	super(Double.toString(value),  width);
	this.setTransferHandler(null);
	this.normalColour = normalColour;
	this.errorColour  = errorColour;
	this.setNormal();
	this.vmin      = vmin;
	this.vmax      = vmax;
	this.increment = increment;
	this.name      = name;
	this.setEnabled(enabled);

	// Now we define the response to keyboard input	
	this.addKeyListener(
			    new KeyAdapter(){
				
				/** Defines response to printing characters. Basically
				 * ignores any but integers, . and -
				 */
				public void keyTyped(KeyEvent event){

				    char c = event.getKeyChar();

				    // Only allowed characters are 0-9, '.' and '-' (if vmin < 0 integers alllowed)
				    if (!Character.isDigit(c) && c != '.' && (DoubleTextField.this.vmin >= 0 || c != '-')){
					getToolkit().beep();
					event.consume();
				    }

				}

				/** Defines what happens when various non-printing keys are pressed.
				 * The up and down arrows increment and decrement the field value.
				 * The page up & down jump up and down by large amounts.
				 */				
				public void keyPressed(KeyEvent event){
				    
				    int n;
				    if(event.getKeyCode() == java.awt.event.KeyEvent.VK_UP){
					
					// Increment
					if((event.getModifiersEx() & (InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) == (InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) {
					    addIncrement(50);
					}else if((event.getModifiersEx() & InputEvent.SHIFT_DOWN_MASK) == InputEvent.SHIFT_DOWN_MASK) {
					    addIncrement(10);
					}else{
					    addIncrement(1);
					}
					
				    }else if(event.getKeyCode() == java.awt.event.KeyEvent.VK_DOWN){
					
					// Decrement					    
					if((event.getModifiersEx() & (InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) == (InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) {
					    subIncrement(50);
					}else if((event.getModifiersEx() & InputEvent.SHIFT_DOWN_MASK) == InputEvent.SHIFT_DOWN_MASK){
					    subIncrement(10);
					}else{
					    subIncrement(1);
					}

				    }else if(event.getKeyCode() == java.awt.event.KeyEvent.VK_PAGE_DOWN){
					
					// Set to minimum value
					setText(Double.toString(DoubleTextField.this.vmin));
					setNormal();
					
				    }else if(event.getKeyCode() == java.awt.event.KeyEvent.VK_PAGE_UP){
					
					// Set to maximum value					    
					setText(Double.toString(DoubleTextField.this.vmax));
					setNormal();
					
				    }else if(event.getKeyCode() == java.awt.event.KeyEvent.VK_DELETE ||
					     event.getKeyCode() == java.awt.event.KeyEvent.VK_BACK_SPACE){
					
					// Delete before cursor position
					int m = getCaretPosition();
					if(m > 0){
					    String text = getText();
					    if(m > 1)
						setText(text.substring(0,m-1) + text.substring(m));
					    else
						setText(text.substring(1));
					    setCaretPosition(m-1);
					}

				    }
				}
			    });

	// Mouse behaviour. Left button increments, right-button decrements. Timers are used
	// to allow automatic updates if buttons are held down. Shift & alt are used as accelerators
	this.addMouseListener(new MouseAdapter() {

		// Set the focus as soon as the mouse is on this field, and 
		// set the caret to the end of it
		public void mouseEntered(MouseEvent event) {
		    // Request the focus (if don't already have it), 
		    if(!hasFocus()) { 
			requestFocus(); 
			setCaretPosition(getText().length());
		    }
		}

		// Increment and decrement with the first and third mouse buttons
		public void mousePressed(MouseEvent event) {

		    int n;
		    if ((event.getModifiersEx() & (InputEvent.BUTTON1_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) == 
			(InputEvent.BUTTON1_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK)) {
			
			addIncrement(50);

			// Initialise timer
			ActionListener taskPerformer = new ActionListener() {
				public void actionPerformed(ActionEvent event) {
				    addIncrement(50);
				}
			    };	

			timerOff();
			incrementTimer = new Timer(DELAY, taskPerformer);	
			incrementTimer.setInitialDelay(INITIAL_DELAY);
			incrementTimer.start();

		    }else if ((event.getModifiersEx() & (InputEvent.BUTTON1_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK) ) == (InputEvent.BUTTON1_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK)) {
			
			addIncrement(10);

			// Initialise timer
			ActionListener taskPerformer = new ActionListener() {
				public void actionPerformed(ActionEvent event) {
				    addIncrement(10);
				}
			    };	

			timerOff();
			incrementTimer = new Timer(DELAY, taskPerformer);	
			incrementTimer.setInitialDelay(INITIAL_DELAY);
			incrementTimer.start();

		    }else if ((event.getModifiersEx() & InputEvent.BUTTON1_DOWN_MASK) == InputEvent.BUTTON1_DOWN_MASK) {
			
			addIncrement(1);

			// Initialise timer
			ActionListener taskPerformer = new ActionListener() {
				public void actionPerformed(ActionEvent event) {
				    addIncrement(1);
				}
			    };	

			timerOff();
			incrementTimer = new Timer(DELAY, taskPerformer);	
			incrementTimer.setInitialDelay(INITIAL_DELAY);
			incrementTimer.start();

		    }else if ((event.getModifiersEx() & (InputEvent.BUTTON3_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) == 
			      (InputEvent.BUTTON3_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK | InputEvent.CTRL_DOWN_MASK)) {

			subIncrement(50);
			
			// Initialise timer
			ActionListener taskPerformer = new ActionListener() {
				public void actionPerformed(ActionEvent event) {
				    subIncrement(50);
				}
			    };	

			timerOff();
			incrementTimer = new Timer(DELAY, taskPerformer);
			incrementTimer.setInitialDelay(INITIAL_DELAY);
			incrementTimer.start();

		    }else if ((event.getModifiersEx() & (InputEvent.BUTTON3_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK) ) == (InputEvent.BUTTON3_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK)) {

			subIncrement(10);

			// Initialise timer
			ActionListener taskPerformer = new ActionListener() {
				public void actionPerformed(ActionEvent event) {
				    subIncrement(10);
				}
			    };	

			timerOff();
			incrementTimer = new Timer(DELAY, taskPerformer);
			incrementTimer.setInitialDelay(INITIAL_DELAY);
			incrementTimer.start();

		    }else if ((event.getModifiersEx() & InputEvent.BUTTON3_DOWN_MASK) == InputEvent.BUTTON3_DOWN_MASK) {
			
			subIncrement(1);

			// Initialise timer
			ActionListener taskPerformer = new ActionListener() {
				public void actionPerformed(ActionEvent event) {
				    subIncrement(1);
				}
			    };	

			timerOff();
			incrementTimer = new Timer(DELAY, taskPerformer);
			incrementTimer.setInitialDelay(INITIAL_DELAY);
			incrementTimer.start();

		    }else if ((event.getModifiersEx() & InputEvent.BUTTON2_DOWN_MASK) == InputEvent.BUTTON2_DOWN_MASK) {

			// Print out information about the field
			System.out.println("DoubleTextField, name = \"" + DoubleTextField.this.name + "\", range = " +
					   DoubleTextField.this.vmin + " to " + DoubleTextField.this.vmax + ", increment = " +
					   DoubleTextField.this.increment);
		    }
		}

		// Switch off timer if button is released
		public void mouseReleased(MouseEvent event) {
		    timerOff();
		}

		// or if mouse is moved off field
		public void mouseExited(MouseEvent event) {
		    timerOff();
		}

	    });

    }

    // Switches off timer
    private void timerOff(){
	if(incrementTimer != null) incrementTimer.stop();
    }

    /** Sets the current value, truncating at minimum and maximum values
     * @param value the new value to set
     */
    public void setValue(double value){
	if(value < this.vmin){
	    value = this.vmin;
	}else if(value > this.vmax){
	    value = this.vmax;
	}
	this.setText(round(value));
	this.setNormal();
    }

    /** Sets the minimum limit. It is not allowed to exceed the current maximum,
     * and if the value goes out of range, the field is set to the error colour
     * @param vmax the new maximum value to set
     */
    public void setVmin(double vmin){
	if(vmin > this.vmax){
	    this.vmin = this.vmax;
	}else{
	    this.vmin = vmin;
	}
    }

    /** Sets the maximum limit, truncating it at the current minimum
     * and altering the displayed value if need be
     * @param vmax the new maximum value to set
     */
    public void setVmax(double vmax){
	if(vmax < this.vmin){
	    this.vmax = this.vmin;
	}else{
	    this.vmax = vmax;
	}
    }

    /** Sets the increment. Must be greater than 0.
     * @param increment the new value to increment by
     */
    public void setIncrement(double increment){
	if(increment < 0)
	    this.increment = 1;
	else
	    this.increment = increment;
    }

    /** Gets the current value, throwing an exception if a problem
     * is encountered
     * @param value the new value to set
     */
    public double getValue() throws Exception {
	try{
	    double f = Double.parseDouble(this.getText().replaceAll(",",""));
	    if(f < vmin || f > vmax)
		throw new OutOfRangeException(name + " is out of range " + vmin + " to " + vmax); 
	    this.setNormal();
	    return f;
	}
	catch(Exception e){
	    this.setError();
	    throw e;
	}
    }

    /** Checks that the current field contains a valid value */
    public boolean checkValue() {
	try{
	    double f = Double.parseDouble(this.getText().replaceAll(",",""));
	    if(f < vmin || f > vmax)
		throw new OutOfRangeException(name + " is out of range " + vmin + " to " + vmax); 
	    this.setNormal();
	    return true;
	}
	catch(Exception e){
	    this.setError();
	    System.out.println(e);
	    return false;
	}
    }

    // Increment the text field by nmult times the standard increment
    public void addIncrement(int nmult){
	try {
	    double f = this.getValue();
	    if(f + nmult*increment > vmax) {
		f  = vmax;
	    }else if(f + nmult*increment < vmin) {
		f  = vmin;
	    }else{
		f += nmult*increment;
		f  = increment*Math.round(f/increment);
	    }
	    setNormal();
	    setText(round(f));
	}
	catch(Exception e){
	    System.out.println(e.toString());
	    System.out.println("Failed to increment field = " + name);
	    setError();
	}					
    }

    // Decrement the text field
    public void subIncrement(int nmult){
	try {
	    double f = this.getValue();
	    if(f - nmult*increment > vmax) {
		f  = vmax;
	    }else if(f - nmult*increment < vmin) {
		f  = vmin;
	    }else{
		f -= nmult*increment;
		f  = increment*Math.round(f/increment);
	    }
	    setNormal();
	    setText(round(f));
	}
	catch(Exception e){
	    System.out.println(e.toString());
	    System.out.println("Failed to decrement field = " + name);
	    setError();
	}					
    }

    public void setNormal() {
	this.setBackground(normalColour);
    }

    public void setError() {
	this.setBackground(errorColour);
    }

    /** Disable past operations */
    public void disablePaste(){
	this.setTransferHandler(null);
    }

    // Converts a double to a string rounding to appropriate number of decimal
    public String round(double f){
	int ndp = increment > 1. ? 1 : (int)(1.-Math.log(increment));
	form.setMaximumFractionDigits(ndp);
	return form.format(f);
    }
	
    /** Exception class to report problems */
    public static class OutOfRangeException extends Exception {
	public OutOfRangeException(String s)
	{
	    super(s);
	}
    }

}
