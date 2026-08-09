/**
 * Audio notification hook for job/task completion.
 * Uses Web Audio API to generate notification sounds.
 */

import { useCallback, useEffect, useState, useRef } from 'react';

// localStorage key for audio notification preference
const AUDIO_ENABLED_KEY = 'pdd-audio-notifications-enabled';

// Shared AudioContext to avoid creating multiple contexts
let sharedAudioContext: AudioContext | null = null;

function getAudioContext(): AudioContext {
  if (!sharedAudioContext) {
    sharedAudioContext = new AudioContext();
  }
  return sharedAudioContext;
}

/**
 * Generate a simple notification sound using Web Audio API
 */
async function playNotificationSound(success: boolean): Promise<void> {
  try {
    const audioContext = getAudioContext();

    // Resume context if suspended (required after page load without user interaction)
    if (audioContext.state === 'suspended') {
      await audioContext.resume();
    }

    if (success) {
      // Success sound: ascending two-tone chime
      playTone(audioContext, 880, 0, 0.15);     // A5
      playTone(audioContext, 1108.73, 0.12, 0.2);  // C#6
    } else {
      // Failure sound: descending two-tone
      playTone(audioContext, 440, 0, 0.2);      // A4
      playTone(audioContext, 349.23, 0.15, 0.25);  // F4
    }
  } catch (error) {
    console.warn('Audio notification failed:', error);
  }
}

/**
 * Play a single tone at the specified frequency
 */
function playTone(
  audioContext: AudioContext,
  frequency: number,
  startTime: number,
  duration: number
): void {
  const oscillator = audioContext.createOscillator();
  const gainNode = audioContext.createGain();

  oscillator.connect(gainNode);
  gainNode.connect(audioContext.destination);

  oscillator.type = 'sine';
  oscillator.frequency.value = frequency;

  // Envelope for smooth sound - louder volume
  const now = audioContext.currentTime;
  gainNode.gain.setValueAtTime(0, now + startTime);
  gainNode.gain.linearRampToValueAtTime(0.5, now + startTime + 0.02);  // Peak volume for clear but non-intrusive notification
  gainNode.gain.exponentialRampToValueAtTime(0.01, now + startTime + duration);

  oscillator.start(now + startTime);
  oscillator.stop(now + startTime + duration);
}

export interface UseAudioNotificationReturn {
  /** Whether audio notifications are enabled */
  audioEnabled: boolean;
  /** Toggle audio notifications on/off */
  setAudioEnabled: (enabled: boolean) => void;
  /** Play a notification sound (respects enabled setting) */
  playNotification: (success: boolean) => void;
  /** Play notification sound regardless of setting (for testing) */
  testSound: (success: boolean) => void;
}

/**
 * Hook for managing audio notifications
 */
export function useAudioNotification(): UseAudioNotificationReturn {
  const [audioEnabled, setAudioEnabledState] = useState<boolean>(() => {
    try {
      const stored = localStorage.getItem(AUDIO_ENABLED_KEY);
      return stored === null ? true : stored === 'true';
    } catch {
      return true;
    }
  });

  // Use ref to avoid stale closures in callbacks passed to other hooks
  const audioEnabledRef = useRef(audioEnabled);
  audioEnabledRef.current = audioEnabled;

  // Persist preference to localStorage
  const setAudioEnabled = useCallback((enabled: boolean) => {
    setAudioEnabledState(enabled);
    try {
      localStorage.setItem(AUDIO_ENABLED_KEY, String(enabled));
    } catch {
      // Ignore storage errors
    }
  }, []);

  // Play notification sound if enabled
  // Uses ref so this function is stable and doesn't cause stale closure issues
  const playNotification = useCallback((success: boolean) => {
    if (audioEnabledRef.current) {
      playNotificationSound(success);
    }
  }, []);

  // Play sound regardless of setting (for testing)
  const testSound = useCallback((success: boolean) => {
    playNotificationSound(success);
  }, []);

  return {
    audioEnabled,
    setAudioEnabled,
    playNotification,
    testSound,
  };
}
