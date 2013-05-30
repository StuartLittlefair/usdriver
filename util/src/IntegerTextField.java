package warwick.marsh.util;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.text.*;

/** Subclass of JTextField for range-checked integer input. Supports
 * up and down arrows and left and right mouse buttons to increment 
 * and decrement the value.  Focus-follows-mouse behaviour. Also
 * allows finer control with a set of 'allowed values', e.g. 1, 2, 4, 8
 */

public class IntegerTextField extends JTextField {

    // The time between updates of the field when the mouse is held down, millisecs
    private static final int DELAY = 20;

    // The time between updates at the start to allow user to add one
    private static final int INITIAL_DELAY = 300;    

    private int    vmin;
    private int    vmax;
    private int    increment;
    private String name;
    private Color  normalColour;
    private Color  errorColour;

    // Increment/decrement timer
    private Timer  incrementTimer = null;

    private int[]  specialValue = null;
    private int[]  allowedValue = null;
    private int    allowedIndex = 0; // initial index if we are restructed to allowed values 

    /** Constructor with an intial value, a range and an indicator of whether the field
     * is enabled.
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

    public IntegerTextField(int value, int vmin, int vmax, int increment, String name, boolean enabled, 
			    Color normalColour, Color errorColour, int width) {
	
	super(Integer.toString(value),  width);
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
				 * ignores any but integers and -
				 */
				public void keyTyped(KeyEvent event){

				    if(allowedValue == null){
					char c = event.getKeyChar();

					// Only allowed characters are 0-9 and '-' (if -ve integers alllowed)
					if (!Character.isDigit(c) && (IntegerTextField.this.vmin >= 0 || c != '-')){
					    getToolkit().beep();
					    event.consume();
					}
				    }else{
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
					if(allowedValue == null){
					    setText(Integer.toString(IntegerTextField.this.vmin));
					    setNormal();
					}else{
					    setText(Integer.toString(allowedValue[0]));
					}
					
				    }else if(event.getKeyCode() == java.awt.event.KeyEvent.VK_PAGE_UP){
					
					if(allowedValue == null){
					    // Set to maximum value					    
					    setText(Integer.toString(IntegerTextField.this.vmax));
					    setNormal();
					}else{
					    setText(Integer.toString(allowedValue[allowedValue.length-1]));
					}
					
				    }else if(event.getKeyCode() == java.awt.event.KeyEvent.VK_DELETE ||
					     event.getKeyCode() == java.awt.event.KeyEvent.VK_BACK_SPACE){
					
					if(allowedValue == null){
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
					}else{
					    event.consume();
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
		    if(isEnabled()){
			// Request the focus (if don't already have it), 
			if(!hasFocus()) { 
			    requestFocus(); 
			    setCaretPosition(getText().length());
			}
		    }
		}

		// Increment and decrement with the first and third mouse buttons
		public void mousePressed(MouseEvent event) {

		    if(isEnabled()){
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
			    
			}else if ((event.getModifiersEx() & (InputEvent.BUTTON1_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) == (InputEvent.BUTTON1_DOWN_MASK | InputEvent.CTRL_DOWN_MASK)) {
			    
			    upToNext();
			    
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
			    
			}else if ((event.getModifiersEx() & (InputEvent.BUTTON3_DOWN_MASK | InputEvent.CTRL_DOWN_MASK) ) == (InputEvent.BUTTON3_DOWN_MASK | InputEvent.CTRL_DOWN_MASK)) {
			    
			    downToNext();
			    
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
			    System.out.println("IntegerTextField, name = \"" + IntegerTextField.this.name + "\", range = " +
					       IntegerTextField.this.vmin + " to " + IntegerTextField.this.vmax + ", increment = " +
					       IntegerTextField.this.increment);
			    if(IntegerTextField.this.specialValue == null){
				System.out.println("There are no special values associated with this field");
			    }else{
				System.out.print("Special values:");
				for(int i=0; i<IntegerTextField.this.specialValue.length-1; i++)
				    System.out.print(" " + IntegerTextField.this.specialValue[i] + ",");
				System.out.println(" " + IntegerTextField.this.specialValue[IntegerTextField.this.specialValue.length-1]);
			    }
			    if(IntegerTextField.this.allowedValue == null){
				System.out.println("There are no allowed values implemented with this field");
			    }else{
				System.out.print("Allowed values:");
				for(int i=0; i<IntegerTextField.this.allowedValue.length-1; i++)
				    System.out.print(" " + IntegerTextField.this.allowedValue[i] + ",");
				System.out.println(" " + IntegerTextField.this.allowedValue[IntegerTextField.this.allowedValue.length-1]);
			    }
			}
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
	if(incrementTimer != null)
	    incrementTimer.stop();
    }
    
    /** Set special values which must ascend monotonically. These are values
     * that can be jumped between using the left and right mouse buttons together with
     * the control key.
     * @param special array of special values
     */
    public void setSpecial(int[] special){
	specialValue = special;
    }

    /** Set allowed values which must ascend monotonically. This restricts the possible 
     * values of the field. They must lie within the range defined by vmin and vmax
     * and if you change vmin or vmax you might have to rerun this function.
     * @param allowed array of allowed values
     */
    public void setAllowed(int[] allowed){
	allowedValue = allowed;
    }

    /** Sets the current value, truncating at minimum and maximum values
     * @param value the new value to set
     */
    public void setValue(int value){
	if(value < this.vmin){
	    value = this.vmin;
	}else if(value > this.vmax){
	    value = this.vmax;
	}
	this.setText(Integer.toString(value));
	this.setNormal();
    }

    /** Sets the minimum limit. It is not allowed to exceed the current maximum,
     * and if the value goes out of range, the field is set to the error colour
     * @param vmax the new maximum value to set
     */
    public void setVmin(int vmin){
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
    public void setVmax(int vmax){
	if(vmax < this.vmin){
	    this.vmax = this.vmin;
	}else{
	    this.vmax = vmax;
	}
    }

    /** Sets the increment. Must be greater than or equal to 1.
     * @param increment the new value to increment by
     */
    public void setIncrement(int increment){
	if(increment < 1)
	    this.increment = 1;
	else
	    this.increment = increment;
    }

    /** Gets the current value, throwing an exception if a problem
     * is encountered
     * @param value the new value to set
     */
    public int getValue() throws Exception {
	try{
	    int n = Integer.parseInt(this.getText().replaceAll(",",""));
	    if(n < vmin || n > vmax)
		throw new OutOfRangeException(name + " is out of range " + vmin + " to " + vmax); 
	    this.setNormal();
	    return n;
	}
	catch(Exception e){
	    //	    System.out.println(e.toString());
	    this.setError();
	    throw e;
	}
    }

    /** Checks that the current field contains a valid value */
    public boolean checkValue() {
	try{
	    int n = Integer.parseInt(this.getText().replaceAll(",",""));
	    if(n < vmin || n > vmax)
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

    /** Increment the text field by nmult times the standard increment, unless
     * allowed values are implemented in which we just jump to the next
     * @param nmult the multiplier of the standard increment to apply
     */
    public void addIncrement(int nmult){
	try {

	    if(allowedValue == null){
		int n = this.getValue();
		if(n + nmult*increment > vmax) {
		    n  = vmax;
		}else if(n + nmult*increment < vmin) {
		    n  = vmin;
		}else{
		    n += nmult*increment;
		    n  = increment * (int)( n / (double)increment + 0.5);
		}
		setNormal();
		setText(Integer.toString(n));
	    }else{

		if(allowedIndex < allowedValue.length - 1){
		    allowedIndex++;
		    setText(Integer.toString(allowedValue[allowedIndex]));
		}

	    }

	}
	catch(Exception e){
	    System.out.println(e.toString());
	    System.out.println("Failed to increment field = " + name);
	    setError();
	}					
    }

    /** Tries to jump to next higher specialValue/allowedValue if there is one */
    public void upToNext(){
	try {
	    if(allowedValue == null){
		int n = this.getValue();
		if(specialValue != null){
		    for(int i=0; i<specialValue.length; i++){
			if(n < specialValue[i] && specialValue[i] % increment == 0){
			    setNormal();
			    setText(Integer.toString(specialValue[i]));
			    return;
			}
		    }
		    System.out.println("There is no special value set higher than the current value of \"" + name + "\" that is compatible with the increment = " + increment);
		}else{
		    System.out.println("There are no special values for " + name);
		}
	    }else{
		if(allowedIndex < allowedValue.length - 1){
		    allowedIndex++;
		    setText(Integer.toString(allowedValue[allowedIndex]));
		}
	    }

	}
	catch(Exception e){
	    System.out.println(e.toString());
	    System.out.println("Failed to jump to next higher special value = " + name);
	    setError();
	}					
    }

    /** Decrement the text field with a multiplier times the normal value
     * @param numult the multiplier of the normal decrement
     */
    public void subIncrement(int nmult){
	try {

	    if(allowedValue == null){
		int n = this.getValue();
		if(n - nmult*increment > vmax) {
		    n  = vmax;
		}else if(n - nmult*increment < vmin) {
		    n  = vmin;
		}else{
		    n -= nmult*increment;
		    n  = increment * (int)( n / (double)increment + 0.5);
		}
		setNormal();
		setText(Integer.toString(n));
	    }else{
		if(allowedIndex > 0){
		    allowedIndex--;
		    setText(Integer.toString(allowedValue[allowedIndex]));
		}
	    }

	}
	catch(Exception e){
	    System.out.println(e.toString());
	    System.out.println("Failed to decrement field = " + name);
	    setError();
	}					
    }

    /** Tries to jump to next lower specialValue if there is one */
    public void downToNext(){
	try {
	    if(allowedValue == null){
		int n = this.getValue();
		if(specialValue != null){
		    for(int i=specialValue.length; i>0; i--){
			if(n > specialValue[i-1] && specialValue[i-1] % increment == 0){
			    setNormal();
			    setText(Integer.toString(specialValue[i-1]));
			    return;
			}
		    }
		    System.out.println("There is no special value set lower than the current value of \"" + name + "\" that is compatible with the increment = " + increment);
		}else{
		    System.out.println("There are no special values for " + name);
		}
	    }else{
		if(allowedIndex > 0){
		    allowedIndex--;
		    setText(Integer.toString(allowedValue[allowedIndex]));
		}
	    }
	}
	catch(Exception e){
	    System.out.println(e.toString());
	    System.out.println("Failed to jump to next lower special value = " + name);
	    setError();
	}					
    }

    /** Sets the background colour to its standard value */
    public void setNormal() {
	this.setBackground(normalColour);
    }

    /** Sets the background colour to its error value */
    public void setError() {
	this.setBackground(errorColour);
    }

    /** Disable past operations */
    public void disablePaste(){
	this.setTransferHandler(null);
    }

    /** Exception class to report problems */
    public static class OutOfRangeException extends Exception {
	public OutOfRangeException(String s)
	{
	    super(s);
	}
    }

}
