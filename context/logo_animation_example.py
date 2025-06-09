import time
# Assuming the 'pdd' package is in your PYTHONPATH or current working directory's parent.
from pdd.branding_animation import start_logo_animation, stop_logo_animation

def main() -> None:
    """
    Demonstrates the usage of the PDD branding animation.
    """
    print("Starting the PDD branding animation...")
    print("The animation will take over the terminal screen.")
    print("Look for the animation in your terminal window.")

    # Start the animation. It runs in a background thread.
    start_logo_animation()

    # Allow the animation to run for a certain period.
    # The animation sequence (formation, hold, expansion) takes about:
    # LOGO_FORMATION_DURATION (1.5s) + LOGO_HOLD_DURATION (1.0s) + 
    # LOGO_TO_BOX_TRANSITION_DURATION (1.5s) = 4.0 seconds.
    # We'll let it run a bit longer to see the final state before stopping.
    # The animation will hold its final frame until stop_logo_animation is called.
    animation_view_duration_seconds: float = 7.0 
    
    print(f"Main program continues to run. Waiting for {animation_view_duration_seconds} seconds...")
    
    # Simulate main program work
    for i in range(int(animation_view_duration_seconds)):
        # Note: Print statements here might be overwritten by the full-screen animation.
        # They will be visible once the animation stops or if it doesn't use screen=True.
        # However, the provided module uses screen=True, so these prints won't be visible
        # until after stop_logo_animation() restores the normal terminal.
        time.sleep(1)
        # print(f"Main program working... {i+1}/{int(animation_view_duration_seconds)}")


    print("Attempting to stop the branding animation...")
    # Stop the animation and wait for the thread to clean up.
    stop_logo_animation()

    print("Branding animation stopped.")
    print("Terminal control returned to the main program.")

if __name__ == "__main__":
    main()
