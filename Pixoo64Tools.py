#
# Pixoo 64 Advanced Tools
#
# A Python application with a graphical user interface (GUI) to control a Divoom Pixoo 64 display.
# This script allows for screen streaming, single image/GIF display, mixed-media playlists,
# a live system performance monitor, a powerful custom text displayer, and a live audio visualizer.
#
# Main libraries used:
# - tkinter: For the GUI components.
# - Pillow (PIL): For all image processing, including GIFs and text rendering.
# - pixoo-python: For communicating with the Pixoo 64 device.
# - psutil: For fetching system CPU and RAM statistics.
# - numpy & soundcard: For the audio visualizer.
#
import logging
import time
import threading
import json
import os
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
from PIL import ImageGrab, Image, ImageTk, ImageDraw, ImageFilter, ImageSequence, ImageFont
from pixoo import Pixoo
import psutil
import numpy as np
import soundcard as sc
import warnings

# Suppress the specific, harmless warning from the soundcard library
warnings.filterwarnings('ignore', category=sc.SoundcardRuntimeWarning)

# Sets up how logs are displayed. Useful for debugging.
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# --- Global State and Configuration ---

pixoo = None
CONFIG_FILE = 'config.json'

streaming = threading.Event()
playlist_active = threading.Event()
gif_active = threading.Event()
sysmon_active = threading.Event()
text_active = threading.Event()
equalizer_active = threading.Event()
ALL_EVENTS = [streaming, playlist_active, gif_active, sysmon_active, text_active, equalizer_active]

show_grid = True
resize_method = Image.Resampling.BICUBIC
last_source_image = None
playlist_files = []
current_gif_path = None
processed_gif_frames = [] 
text_color = (255, 255, 255)
outline_color = (0, 0, 0)
font_path = None

vortex_angle = 0
vortex_particles = []

filter_options = {
    "NONE": None, "BLUR": ImageFilter.BLUR, "CONTOUR": ImageFilter.CONTOUR,
    "DETAIL": ImageFilter.DETAIL, "EDGE_ENHANCE": ImageFilter.EDGE_ENHANCE,
    "EDGE_ENHANCE_MORE": ImageFilter.EDGE_ENHANCE_MORE, "EMBOSS": ImageFilter.EMBOSS,
    "FIND_EDGES": ImageFilter.FIND_EDGES, "SHARPEN": ImageFilter.SHARPEN,
    "SMOOTH": ImageFilter.SMOOTH, "SMOOTH_MORE": ImageFilter.SMOOTH_MORE
}

# --- Configuration Management ---

def load_config():
    """Loads settings from the config file, creating it if it doesn't exist."""
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, 'r') as f:
            return json.load(f)
    return {}

def save_config(data):
    """Saves the given data to the config file."""
    with open(CONFIG_FILE, 'w') as f:
        json.dump(data, f, indent=4)

app_config = load_config()
DEFAULT_PIXOO_IP = app_config.get('ip_address', '')

# --- Core Functions ---

def stop_all_activity():
    if gif_active.is_set() or text_active.is_set(): 
        toggle_processing_controls(enabled=True)
    for event in ALL_EVENTS:
        if event.is_set():
            logging.info(f"Stopping task associated with {event}")
            event.clear()
    time.sleep(0.1)

def connect_to_pixoo(ip_address: str) -> bool:
    global pixoo
    try:
        logging.info(f"Connecting to Pixoo at IP: {ip_address}")
        stop_all_activity()
        new_pixoo = Pixoo(ip_address)
        logging.info("Successfully connected to Pixoo.")
        pixoo = new_pixoo
        app_config['ip_address'] = ip_address
        save_config(app_config)
        return True
    except Exception as e:
        logging.error(f"Failed to connect to Pixoo: {e}")
        return False

def draw_grid(image):
    if not show_grid: return image
    draw = ImageDraw.Draw(image)
    width, height = image.size
    for x in range(0, width, 8):
        draw.line([(x, 0), (x, height)], fill=(200, 200, 200), width=1)
    for y in range(0, height, 8):
        draw.line([(0, y), (width, y)], fill=(200, 200, 200), width=1)
    return image

def update_preview_label(image: Image.Image):
    try:
        preview_image = image.resize((512, 512), Image.Resampling.NEAREST)
        preview_image = draw_grid(preview_image)
        preview_image_tk = ImageTk.PhotoImage(preview_image)
        preview_label.config(image=preview_image_tk)
        preview_label.image = preview_image_tk
    except Exception as e:
        logging.error(f"Failed to update preview label: {e}")

def crop_center(image):
    width, height = image.size
    new_edge = min(width, height)
    left = (width - new_edge) // 2
    top = (height - new_edge) // 2
    right = left + new_edge
    bottom = top + new_edge
    return image.crop((left, top, right, bottom))

def process_image(image):
    global last_source_image
    last_source_image = image.copy()
    if crop_to_square_mode.get():
        image = crop_center(image)
    processed = image.resize((64, 64), resize_method)
    selected_filter = filter_mode_var.get()
    if selected_filter != "NONE" and filter_options[selected_filter] is not None:
        processed = processed.filter(filter_options[selected_filter])
    return processed

def refresh_preview():
    if last_source_image is not None:
        processed_image = process_image(last_source_image)
        update_preview_label(processed_image)

#
# Background Tasks (run in separate threads)
#

def screen_capture_task():
    while streaming.is_set():
        if pixoo is None: time.sleep(0.5); continue
        try:
            bbox = None
            if use_region_var.get():
                try:
                    x, y, w, h = int(region_x_entry.get()), int(region_y_entry.get()), int(region_w_entry.get()), int(region_h_entry.get())
                    bbox = (x, y, x + w, y + h)
                except ValueError: logging.warning("Invalid screen region. Using full screen.")
            screenshot = ImageGrab.grab(bbox=bbox)
            processed = process_image(screenshot)
            pixoo.draw_image(processed); pixoo.push()
            update_preview_label(processed)
        except Exception as e:
            logging.error(f"Error during screen capture: {e}"); streaming.clear(); break
        time.sleep(1/60)

def sysmon_task():
    font = None; psutil.cpu_percent(interval=None) 
    while sysmon_active.is_set():
        if pixoo is None: time.sleep(1); continue
        try:
            cpu_percent, mem_percent = psutil.cpu_percent(interval=1), psutil.virtual_memory().percent
            img = Image.new('RGB', (64, 64), 'black'); draw = ImageDraw.Draw(img)
            draw.text((4, 5), "CPU", fill=(255, 255, 255), font=font)
            cpu_bar_height = int(60 * (cpu_percent / 100))
            draw.rectangle([5, 62 - cpu_bar_height, 25, 62], fill=(0, 150, 255))
            draw.text((4, 50 - cpu_bar_height), f"{int(cpu_percent)}%", fill='white', font=font)
            draw.text((36, 5), "RAM", fill=(255, 255, 255), font=font)
            mem_bar_height = int(60 * (mem_percent / 100))
            draw.rectangle([38, 62 - mem_bar_height, 58, 62], fill=(0, 255, 150))
            draw.text((36, 50 - mem_bar_height), f"{int(mem_percent)}%", fill='white', font=font)
            pixoo.draw_image(img); pixoo.push()
            update_preview_label(img)
        except Exception as e:
            logging.error(f"Error in system monitor: {e}"); sysmon_active.clear()
    logging.info("System monitor stopped.")


def play_gif_once_in_playlist(gif_path):
    MIN_FRAME_DURATION_S = 0.02
    try:
        with Image.open(gif_path) as gif:
            for frame_image in ImageSequence.Iterator(gif):
                start_time = time.monotonic()
                if not playlist_active.is_set(): break
                if pixoo is None: time.sleep(1); continue
                frame_rgb = frame_image.convert("RGB"); processed = process_image(frame_rgb)
                pixoo.draw_image(processed); pixoo.push()
                update_preview_label(processed)
                duration_s = frame_image.info.get('duration', 100) / 1000.0
                if duration_s < MIN_FRAME_DURATION_S: duration_s = MIN_FRAME_DURATION_S
                elapsed_s = time.monotonic() - start_time
                time_to_wait = duration_s - elapsed_s
                if time_to_wait > 0: playlist_active.wait(time_to_wait)
    except Exception as e:
        logging.error(f"Could not play playlist GIF '{gif_path}': {e}"); time.sleep(2)

def playlist_task(interval_s):
    while playlist_active.is_set():
        if not playlist_files: logging.warning("Playlist is empty, stopping."); break
        for item_path in playlist_files:
            if not playlist_active.is_set(): break
            if item_path.lower().endswith('.gif'):
                logging.info(f"Playing GIF from playlist: {item_path}")
                play_gif_once_in_playlist(item_path)
            else:
                logging.info(f"Displaying image from playlist: {item_path} for {interval_s}s")
                try:
                    image = Image.open(item_path).convert("RGB"); processed = process_image(image)
                    pixoo.draw_image(processed); pixoo.push()
                    update_preview_label(processed)
                    for _ in range(interval_s):
                        if not playlist_active.is_set(): break 
                        time.sleep(1)
                except Exception as e:
                    logging.error(f"Error cycling image '{item_path}': {e}"); time.sleep(2)
        if not playlist_active.is_set(): break
    logging.info("Playlist cycle finished.")

def preprocess_gif_task():
    global processed_gif_frames; processed_gif_frames.clear()
    if not current_gif_path: return
    try:
        with Image.open(current_gif_path) as gif:
            for i, frame_image in enumerate(ImageSequence.Iterator(gif)):
                gif_path_label.config(text=f"Processing frame {i+1}...")
                frame_rgb = frame_image.convert("RGB"); processed = process_image(frame_rgb)
                duration = frame_image.info.get('duration', 100)
                processed_gif_frames.append({'image': processed, 'duration': duration})
        gif_path_label.config(text=f"Ready: {current_gif_path.split('/')[-1]}")
        gif_active.set(); threading.Thread(target=gif_playback_task, daemon=True).start()
    except Exception as e:
        messagebox.showerror("GIF Error", f"Could not process GIF: {e}")
        gif_path_label.config(text="GIF processing failed."); toggle_processing_controls(enabled=True)

def gif_playback_task():
    if not processed_gif_frames: return
    MIN_FRAME_DURATION_S = 0.02
    while gif_active.is_set():
        for frame_data in processed_gif_frames:
            start_time = time.monotonic()
            if not gif_active.is_set(): break
            if pixoo is None: time.sleep(1); continue
            try:
                frame_image = frame_data['image']; pixoo.draw_image(frame_image); pixoo.push()
                update_preview_label(frame_image)
                duration_s = frame_data['duration'] / 1000.0
                if duration_s < MIN_FRAME_DURATION_S: duration_s = MIN_FRAME_DURATION_S
                elapsed_s = time.monotonic() - start_time
                time_to_wait = duration_s - elapsed_s
                if time_to_wait > 0: gif_active.wait(time_to_wait)
            except Exception as e:
                logging.error(f"Error during GIF playback: {e}"); gif_active.clear(); break
        if not gif_active.is_set(): break
    logging.info("GIF playback finished."); toggle_processing_controls(enabled=True)

def text_animation_task(text, font, text_color, outline_color, x_pos, y_pos, delay_ms):
    try:
        left, top, right, bottom = font.getbbox(text)
        text_width, text_height = right - left, bottom - top
        
        full_text_image = Image.new('RGBA', (text_width, text_height))
        draw = ImageDraw.Draw(full_text_image)
        draw.text((0, -top), text, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
        
        x = 64
        while text_active.is_set():
            frame = Image.new('RGB', (64, 64), (0,0,0))
            frame.paste(full_text_image, (x, y_pos), full_text_image) 
            pixoo.draw_image(frame); pixoo.push()
            update_preview_label(frame)
            
            x -= 1 # Move left
            if x < -text_width: # Reset when text is fully off-screen.
                x = 64
            
            time.sleep(delay_ms / 1000.0)
    except Exception as e:
        logging.error(f"Error during text animation: {e}")
    toggle_processing_controls(enabled=True)

def equalizer_task(device_id, effect):
    global vortex_angle, vortex_particles
    bar_heights = np.zeros(16)
    vortex_angle = 0
    vortex_particles = []

    try:
        with sc.get_microphone(id=device_id, include_loopback=True).recorder(samplerate=44100) as mic:
            while equalizer_active.is_set():
                if pixoo is None: time.sleep(0.1); continue
                
                data = mic.record(numframes=2048)
                if data is None or len(data) == 0: continue
                if data.ndim > 1: data = data[:, 0]

                if effect == "Classic Bars":
                    img = draw_classic_bars(data, bar_heights)
                elif effect == "Radial Pulse":
                    img = draw_radial_pulse(data)
                elif effect == "Vortex":
                    img = draw_vortex(data)
                else:
                    img = Image.new('RGB', (64, 64), (0,0,0))
                
                pixoo.draw_image(img); pixoo.push()
                update_preview_label(img)
    except Exception as e:
        logging.error(f"Audio visualizer failed: {e}")
        messagebox.showerror("Visualizer Error", f"The audio visualizer failed. The selected device may no longer be available.\n\nError: {e}")
    equalizer_active.clear()

# --- Visualizer Drawing Functions ---

def draw_classic_bars(data, bar_heights, num_bars=16):
    fft_magnitude = np.abs(np.fft.rfft(data * np.hanning(len(data))))
    img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
    bar_width = 64 / num_bars

    for i in range(num_bars):
        low_freq = int(len(fft_magnitude) * (i / num_bars))
        high_freq = int(len(fft_magnitude) * ((i + 1) / num_bars))
        magnitude = np.mean(fft_magnitude[low_freq:high_freq])
        
        target_height = min(63, int(np.log1p(magnitude) * 8))
        bar_heights[i] = max(target_height, bar_heights[i] * 0.7 - 2)
        
        if bar_heights[i] > 0:
            hue = int(i * (360 / num_bars))
            color = f"hsl({hue}, 100%, 50%)"
            x0, y0 = i * bar_width, 63 - bar_heights[i]
            x1, y1 = (i + 1) * bar_width - 1, 63
            draw.rectangle([x0, y0, x1, y1], fill=color)
    return img

def draw_radial_pulse(data, num_lines=16):
    fft_magnitude = np.abs(np.fft.rfft(data * np.hanning(len(data))))
    img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
    center_x, center_y = 31, 31

    for i in range(num_lines):
        angle = (i / num_lines) * 2 * np.pi
        low_freq = int(len(fft_magnitude) * (i / num_lines))
        high_freq = int(len(fft_magnitude) * ((i + 1) / num_lines))
        magnitude = np.mean(fft_magnitude[low_freq:high_freq])
        
        length = min(32, int(np.log1p(magnitude) * 4))
        
        if length > 1:
            hue = int((angle * (180/np.pi)) % 360)
            color = f"hsl({hue}, 100%, 50%)"
            end_x = center_x + length * np.cos(angle)
            end_y = center_y + length * np.sin(angle)
            draw.line([center_x, center_y, end_x, end_y], fill=color, width=2)
    return img

def draw_vortex(data):
    global vortex_angle, vortex_particles
    volume = np.mean(np.abs(data))
    bass_freqs = np.fft.rfft(data * np.hanning(len(data)))
    bass = np.mean(np.abs(bass_freqs[0:100]))
    
    img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
    center_x, center_y = 31, 31
    
    vortex_angle += 0.05 + bass * 0.003
    
    if len(vortex_particles) < 120 and volume > 0.01:
        vortex_particles.append([0, np.random.uniform(0, 2*np.pi), np.random.uniform(0.2, 1.2)])

    new_particles = []
    for p in vortex_particles:
        radius, angle, speed = p
        radius += speed
        if radius < 32:
            angle += speed * 0.1
            hue = int(((angle * 180/np.pi) + vortex_angle * 50) % 360)
            color = f"hsl({hue}, 100%, {int(50 + radius * 1.5)}%)"
            x = center_x + radius * np.cos(angle + vortex_angle)
            y = center_y + radius * np.sin(angle + vortex_angle)
            draw.point((x,y), fill=color)
            new_particles.append([radius, angle, speed])
    vortex_particles = new_particles
    return img


#
# GUI Actions (functions called by button clicks)
#

def on_connect_button_click():
    ip = ip_entry.get().strip();
    if connect_to_pixoo(ip): messagebox.showinfo("Success", f"Connected to Pixoo at {ip}")
    else: messagebox.showerror("Failed", f"Could not connect to Pixoo at {ip}")

def toggle_processing_controls(enabled=True):
    state = "readonly" if enabled else "disabled"
    for widget in [resize_mode_combobox, filter_combobox, font_size_spinbox, pos_x_spinbox, pos_y_spinbox]:
        widget.config(state=state)
    crop_checkbutton.config(state="normal" if enabled else "disabled")


def start_streaming(): stop_all_activity(); streaming.set(); threading.Thread(target=screen_capture_task, daemon=True).start()
def start_sysmon(): stop_all_activity(); sysmon_active.set(); threading.Thread(target=sysmon_task, daemon=True).start()

def browse_image():
    stop_all_activity(); path = filedialog.askopenfilename(filetypes=[("Images", "*.png;*.jpg;*.jpeg;*.bmp")])
    if not path: return
    try: image = Image.open(path).convert("RGB"); processed = process_image(image); pixoo.draw_image(processed); pixoo.push(); update_preview_label(processed)
    except Exception as e: messagebox.showerror("Error", f"Failed to process image: {e}")

def browse_gif():
    global current_gif_path; stop_all_activity(); path = filedialog.askopenfilename(filetypes=[("GIFs", "*.gif")])
    if not path: return
    current_gif_path = path; gif_path_label.config(text=f"Selected: {path.split('/')[-1]}")
    try:
        with Image.open(path) as gif: processed = process_image(gif.convert("RGB")); update_preview_label(processed)
    except Exception as e: messagebox.showerror("Error", f"Failed to load GIF preview: {e}")

def start_gif():
    stop_all_activity();
    if not current_gif_path: messagebox.showerror("Error", "No GIF file loaded."); return
    toggle_processing_controls(enabled=False); gif_path_label.config(text="Processing GIF...")
    threading.Thread(target=preprocess_gif_task, daemon=True).start()

def start_playlist():
    stop_all_activity();
    if not playlist_files: messagebox.showwarning("Empty", "Playlist is empty."); return
    try:
        interval_value = int(interval_spinbox.get());
        if interval_value < 1: interval_value = 5
    except (ValueError, tk.TclError): interval_value = 5
    playlist_active.set(); threading.Thread(target=playlist_task, args=(interval_value,), daemon=True).start()

def add_to_playlist():
    files = filedialog.askopenfilenames(filetypes=[("All Media", "*.png;*.jpg;*.jpeg;*.bmp;*.gif"), ("Image Files", "*.png;*.jpg;*.jpeg;*.bmp"), ("GIF Files", "*.gif")])
    for f in files:
        if f not in playlist_files: playlist_files.append(f); playlist_listbox.insert(tk.END, f.split('/')[-1])

def remove_from_playlist():
    indices = sorted(playlist_listbox.curselection(), reverse=True)
    for i in indices: playlist_listbox.delete(i); playlist_files.pop(i)

def clear_playlist(): stop_all_activity(); playlist_files.clear(); playlist_listbox.delete(0, tk.END)

def save_playlist():
    if not playlist_files: messagebox.showwarning("Empty", "Playlist is empty."); return
    path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Playlist Files", "*.txt")])
    if not path: return
    try:
        with open(path, 'w') as f:
            for file_path in playlist_files: f.write(f"{file_path}\n")
        messagebox.showinfo("Success", f"Playlist saved to {path}")
    except Exception as e: messagebox.showerror("Error", f"Could not save playlist: {e}")
        
def load_playlist():
    path = filedialog.askopenfilename(filetypes=[("Playlist Files", "*.txt")])
    if not path: return
    clear_playlist() 
    try:
        with open(path, 'r') as f:
            for line in f:
                file_path = line.strip()
                if file_path: playlist_files.append(file_path); playlist_listbox.insert(tk.END, file_path.split('/')[-1])
    except Exception as e: messagebox.showerror("Error", f"Could not load playlist: {e}")

def update_text_preview(event=None):
    try:
        text = text_entry.get("1.0", "end-1c")
        if not text: update_preview_label(Image.new('RGB', (64,64), (0,0,0))); return
        size, x, y = int(font_size_spinbox.get()), int(pos_x_spinbox.get()), int(pos_y_spinbox.get())
        font = ImageFont.load_default()
        if font_path:
            try: font = ImageFont.truetype(font_path, size)
            except IOError: logging.warning(f"Could not load font: {font_path}. Using default.")
        img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
        draw.text((x, y), text, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
        update_preview_label(img)
    except (ValueError, tk.TclError): pass
    except Exception as e: logging.error(f"Error updating text preview: {e}")

def choose_text_color():
    global text_color; color_code = colorchooser.askcolor(title="Choose Text Color")
    if color_code and color_code[1]: text_color = tuple(int(c) for c in color_code[0]); text_color_preview.config(bg=color_code[1]); update_text_preview()

def choose_outline_color():
    global outline_color; color_code = colorchooser.askcolor(title="Choose Outline Color")
    if color_code and color_code[1]: outline_color = tuple(int(c) for c in color_code[0]); outline_color_preview.config(bg=color_code[1]); update_text_preview()
        
def browse_for_font():
    global font_path; path = filedialog.askopenfilename(filetypes=[("TrueType Fonts", "*.ttf")])
    if path: font_path = path; font_path_label.config(text=f"Font: {path.split('/')[-1]}"); update_text_preview()

def display_text():
    stop_all_activity()
    if pixoo is None: messagebox.showerror("Error", "Not connected to Pixoo."); return
    text = text_entry.get("1.0", "end-1c")
    if not text: pixoo.clear(); pixoo.push(); update_preview_label(Image.new('RGB', (64,64), (0,0,0))); return
    size, x_pos, y_pos, delay_ms = int(font_size_spinbox.get()), int(pos_x_spinbox.get()), int(pos_y_spinbox.get()), int(anim_speed_spinbox.get())
    is_scrolling = scroll_text_var.get()
    
    font = ImageFont.load_default()
    if font_path:
        try: font = ImageFont.truetype(font_path, size)
        except IOError: messagebox.showwarning("Font Error", f"Could not load font. Using default.")
    
    if not is_scrolling:
        img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
        draw.text((x_pos, y_pos), text, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
        pixoo.draw_image(img); pixoo.push(); update_preview_label(img)
    else:
        toggle_processing_controls(enabled=False); text_active.set()
        threading.Thread(target=text_animation_task, args=(text, font, text_color, outline_color, x_pos, y_pos, delay_ms), daemon=True).start()

def populate_audio_devices():
    device_listbox.set(''); device_listbox['values'] = []
    try:
        speakers = sc.all_speakers(); loopbacks = sc.all_microphones(include_loopback=True)
        device_names = [d.name for d in speakers] + [d.name for d in loopbacks if d.isloopback]
        device_listbox['values'] = sorted(list(set(device_names)))
        if device_listbox['values']: device_listbox.set(device_listbox['values'][0])
    except Exception as e:
        logging.error(f"Could not get audio devices: {e}")
        messagebox.showerror("Audio Error", "Could not find any audio devices. Please ensure you have soundcard drivers installed.")

def start_equalizer():
    stop_all_activity()
    if pixoo is None: messagebox.showerror("Error", "Not connected to Pixoo."); return
    device_name = device_listbox.get()
    if not device_name: messagebox.showwarning("No Device", "Please select an audio device first."); return
    
    try:
        device = sc.get_microphone(device_name, include_loopback=True)
        if device is None: device = sc.get_speaker(device_name)
        if device is None: messagebox.showerror("Error", "Could not find the selected device."); return
        
        effect = eq_effect_combobox.get()
        equalizer_active.set()
        threading.Thread(target=equalizer_task, args=(device.id, effect), daemon=True).start()
    except Exception as e:
        messagebox.showerror("Error", f"Failed to start visualizer on '{device_name}'.\n\n{e}")

#
# GUI Setup
#

root = tk.Tk(); root.title("Pixoo 64 Advanced Tools"); style = ttk.Style(root)
main_frame = ttk.Frame(root, padding=10); main_frame.pack(fill="both", expand=True)

ip_frame = ttk.Frame(main_frame); ip_frame.pack(fill="x", pady=(0, 10))
ttk.Label(ip_frame, text="Pixoo IP:").pack(side=tk.LEFT); ip_entry = ttk.Entry(ip_frame); ip_entry.pack(side=tk.LEFT, fill="x", expand=True, padx=5); ip_entry.insert(0, DEFAULT_PIXOO_IP)
connect_button = ttk.Button(ip_frame, text="Connect", command=on_connect_button_click); connect_button.pack(side=tk.LEFT)

notebook = ttk.Notebook(main_frame); notebook.pack(fill="both", expand=True, pady=5)
tab1 = ttk.Frame(notebook, padding=10); notebook.add(tab1, text='Image & Stream')
tab2 = ttk.Frame(notebook, padding=10); notebook.add(tab2, text='Playlist')
tab5 = ttk.Frame(notebook, padding=10); notebook.add(tab5, text='Text Display')
tab6 = ttk.Frame(notebook, padding=10); notebook.add(tab6, text='Equalizer')
tab3 = ttk.Frame(notebook, padding=10); notebook.add(tab3, text='System Monitor')
tab4 = ttk.Frame(notebook, padding=10); notebook.add(tab4, text='Credits')

# Tab 1: Image & Stream
t1_left = ttk.Frame(tab1); t1_left.pack(side=tk.LEFT, fill="both", expand=True, padx=(0,10)); t1_right = ttk.Frame(tab1); t1_right.pack(side=tk.RIGHT, fill="both", expand=True)
preview_label = ttk.Label(t1_right, anchor="center"); preview_label.pack(fill="both", expand=True)
blank_image = ImageTk.PhotoImage(Image.new('RGB', (512, 512), (240, 240, 240))); preview_label.config(image=blank_image)
img_frame = ttk.LabelFrame(t1_left, text="Static Image", padding=5); img_frame.pack(fill="x", pady=5); ttk.Button(img_frame, text="Browse Image", command=browse_image).pack(fill="x")
gif_frame = ttk.LabelFrame(t1_left, text="Animated GIF", padding=5); gif_frame.pack(fill="x", pady=5)
gif_path_label = ttk.Label(gif_frame, text="No GIF loaded."); gif_path_label.pack(fill="x"); gif_btn_frame = ttk.Frame(gif_frame); gif_btn_frame.pack(fill="x", pady=(5,0))
ttk.Button(gif_btn_frame, text="Browse GIF", command=browse_gif).pack(side="left", fill="x", expand=True); ttk.Button(gif_btn_frame, text="Start GIF", command=start_gif).pack(side="left", fill="x", expand=True, padx=(5,0))
stream_frame = ttk.LabelFrame(t1_left, text="Screen Streaming", padding=5); stream_frame.pack(fill="x", pady=5); ttk.Button(stream_frame, text="Start Fullscreen Stream", command=start_streaming).pack(fill="x")
use_region_var = tk.BooleanVar(value=False); ttk.Checkbutton(stream_frame, text="Use Region:", variable=use_region_var).pack(anchor="w", pady=(10,0)); region_frame = ttk.Frame(stream_frame); region_frame.pack(fill="x")
ttk.Label(region_frame, text="X:").pack(side="left"); region_x_entry = ttk.Entry(region_frame, width=5); region_x_entry.pack(side="left"); region_x_entry.insert(0, "0"); ttk.Label(region_frame, text="Y:").pack(side="left"); region_y_entry = ttk.Entry(region_frame, width=5); region_y_entry.pack(side="left"); region_y_entry.insert(0, "0")
ttk.Label(region_frame, text="W:").pack(side="left"); region_w_entry = ttk.Entry(region_frame, width=5); region_w_entry.pack(side="left"); region_w_entry.insert(0, "800"); ttk.Label(region_frame, text="H:").pack(side="left"); region_h_entry = ttk.Entry(region_frame, width=5); region_h_entry.pack(side="left"); region_h_entry.insert(0, "600")
options_frame = ttk.LabelFrame(t1_left, text="Processing Options", padding=5); options_frame.pack(fill="x", pady=5)
resize_mode_var = tk.StringVar(value="BICUBIC"); filter_mode_var = tk.StringVar(value="NONE"); crop_to_square_mode = tk.BooleanVar(value=False); ttk.Label(options_frame, text="Resizing:").pack(anchor="w"); resize_mode_combobox = ttk.Combobox(options_frame, textvariable=resize_mode_var, values=[r.name for r in Image.Resampling if r.name != 'DEFAULT'], state="readonly"); resize_mode_combobox.pack(fill="x")
ttk.Label(options_frame, text="Filter:").pack(anchor="w", pady=(5,0)); filter_combobox = ttk.Combobox(options_frame, textvariable=filter_mode_var, values=list(filter_options.keys()), state="readonly"); filter_combobox.pack(fill="x"); crop_checkbutton = ttk.Checkbutton(options_frame, text="Crop to 1:1 Square", variable=crop_to_square_mode, command=refresh_preview); crop_checkbutton.pack(anchor="w", pady=5)

# Tab 2: Playlist
t2_left = ttk.Frame(tab2); t2_left.pack(side=tk.LEFT, fill="both", expand=True, padx=(0,10)); t2_right = ttk.Frame(tab2); t2_right.pack(side=tk.RIGHT, fill="y")
listbox_frame = ttk.Frame(t2_left); listbox_frame.pack(fill="both", expand=True); playlist_scrollbar = ttk.Scrollbar(listbox_frame, orient=tk.VERTICAL); playlist_listbox = tk.Listbox(listbox_frame, yscrollcommand=playlist_scrollbar.set, selectmode=tk.EXTENDED); playlist_scrollbar.config(command=playlist_listbox.yview); playlist_scrollbar.pack(side=tk.RIGHT, fill=tk.Y); playlist_listbox.pack(side=tk.LEFT, fill="both", expand=True)
ttk.Button(t2_right, text="Add Media", command=add_to_playlist).pack(fill="x", pady=2); ttk.Button(t2_right, text="Remove Sel.", command=remove_from_playlist).pack(fill="x", pady=2); ttk.Button(t2_right, text="Clear All", command=clear_playlist).pack(fill="x", pady=2)
ttk.Separator(t2_right).pack(fill="x", pady=10); ttk.Button(t2_right, text="Save Playlist", command=save_playlist).pack(fill="x", pady=2); ttk.Button(t2_right, text="Load Playlist", command=load_playlist).pack(fill="x", pady=2); ttk.Separator(t2_right).pack(fill="x", pady=10)
ttk.Label(t2_right, text="Interval (s):").pack(); interval_spinbox = tk.Spinbox(t2_right, from_=1, to=3600, width=10, justify=tk.CENTER); interval_spinbox.pack(fill="x", pady=2); interval_spinbox.delete(0, "end"); interval_spinbox.insert(0, "10")
ttk.Button(t2_right, text="START PLAYLIST", command=start_playlist, style="Accent.TButton").pack(fill="x", pady=(10,2)); style.configure("Accent.TButton", foreground="green")

# Tab 3: System Monitor
ttk.Label(tab3, text="Displays real-time CPU and RAM usage on your Pixoo.", justify="center").pack(pady=20); ttk.Button(tab3, text="START SYSTEM MONITOR", command=start_sysmon).pack(pady=10, ipady=10)

# Tab 4: Credits
credits_center_frame = ttk.Frame(tab4); credits_center_frame.pack(expand=True)
title_font = ("Segoe UI", 18, "bold"); author_font = ("Segoe UI", 12, "italic"); header_font = ("Segoe UI", 11, "bold"); body_font = ("Segoe UI", 10); link_font = ("Segoe UI", 10, "underline")
ttk.Label(credits_center_frame, text="Pixoo 64 Advanced Tools", font=title_font).pack(pady=(10, 0)); ttk.Label(credits_center_frame, text="by Doug Farmer", font=author_font).pack(pady=(0, 10))
discord_frame = ttk.Frame(credits_center_frame); discord_frame.pack(pady=5); ttk.Label(discord_frame, text="Discord:", font=body_font).pack(side=tk.LEFT); ttk.Label(discord_frame, text="wtfyd", font=link_font, foreground="#5865F2").pack(side=tk.LEFT)
ttk.Separator(credits_center_frame, orient='horizontal').pack(fill='x', padx=20, pady=20); ttk.Label(credits_center_frame, text="Special Thanks", font=header_font).pack()
ttk.Label(credits_center_frame, text="All credit for the foundational concept and starting point goes to MikeTheTech. This tool was built and expanded upon his great work.", font=body_font, wraplength=400, justify="center").pack(pady=5)
ttk.Separator(credits_center_frame, orient='horizontal').pack(fill='x', padx=20, pady=20); ttk.Label(credits_center_frame, text="More features are coming soon...", font=author_font).pack(pady=10)

# Tab 5: Text Display
t5_left = ttk.Frame(tab5); t5_left.pack(side=tk.LEFT, fill="both", expand=True, padx=(0,10)); t5_right = ttk.Frame(tab5); t5_right.pack(side=tk.LEFT, fill="y")
text_entry_frame = ttk.LabelFrame(t5_left, text="Message", padding=5); text_entry_frame.pack(fill="both", expand=True); text_entry = tk.Text(text_entry_frame, height=5, wrap="word"); text_entry.pack(fill="both", expand=True); text_entry.bind("<KeyRelease>", update_text_preview)
font_frame = ttk.LabelFrame(t5_left, text="Font & Style", padding=5); font_frame.pack(fill="x", pady=5); ttk.Button(font_frame, text="Browse for Font File (.ttf)", command=browse_for_font).pack(fill="x"); font_path_label = ttk.Label(font_frame, text="Font: Default"); font_path_label.pack(anchor="w", pady=2)
style_frame = ttk.Frame(font_frame); style_frame.pack(fill="x", pady=5); ttk.Label(style_frame, text="Size:").pack(side="left"); font_size_spinbox = tk.Spinbox(style_frame, from_=1, to=100, width=4, command=update_text_preview); font_size_spinbox.pack(side="left", padx=(0,10)); font_size_spinbox.delete(0,"end"); font_size_spinbox.insert(0,"16")
ttk.Label(style_frame, text="X:").pack(side="left"); pos_x_spinbox = tk.Spinbox(style_frame, from_=-64, to=64, width=4, command=update_text_preview); pos_x_spinbox.pack(side="left", padx=(0,10)); pos_x_spinbox.delete(0,"end"); pos_x_spinbox.insert(0,"0")
ttk.Label(style_frame, text="Y:").pack(side="left"); pos_y_spinbox = tk.Spinbox(style_frame, from_=-64, to=64, width=4, command=update_text_preview); pos_y_spinbox.pack(side="left"); pos_y_spinbox.delete(0,"end"); pos_y_spinbox.insert(0,"0")
color_frame = ttk.LabelFrame(t5_right, text="Color Options", padding=5); color_frame.pack(fill="x"); ttk.Button(color_frame, text="Text Color", command=choose_text_color).pack(fill="x"); text_color_preview = tk.Label(color_frame, text=" ", bg="#FFFFFF", relief="sunken", width=4); text_color_preview.pack(fill="x", pady=(0,5))
ttk.Button(color_frame, text="Outline Color", command=choose_outline_color).pack(fill="x"); outline_color_preview = tk.Label(color_frame, text=" ", bg="#000000", relief="sunken", width=4); outline_color_preview.pack(fill="x")
anim_frame = ttk.LabelFrame(t5_right, text="Animation", padding=5); anim_frame.pack(fill="x", pady=5)
scroll_text_var = tk.BooleanVar(value=False); ttk.Checkbutton(anim_frame, text="Enable Scrolling", variable=scroll_text_var).pack(anchor='w')
anim_speed_frame = ttk.Frame(anim_frame); anim_speed_frame.pack(fill='x', pady=(5,0))
ttk.Label(anim_speed_frame, text="Scroll Speed (ms):").pack(side='left'); anim_speed_spinbox = tk.Spinbox(anim_speed_frame, from_=10, to=1000, increment=10, width=6); anim_speed_spinbox.pack(side='left', padx=5); anim_speed_spinbox.delete(0,"end"); anim_speed_spinbox.insert(0,"50")
ttk.Button(t5_right, text="DISPLAY TEXT", command=display_text, style="Accent.TButton").pack(fill="x", ipady=5, pady=10)

# Tab 6: Equalizer
eq_top_frame = ttk.Frame(tab6, padding=5); eq_top_frame.pack(fill="x")
ttk.Label(eq_top_frame, text="Audio Device:").pack(side="left", padx=5); device_listbox = ttk.Combobox(eq_top_frame, state="readonly", width=40); device_listbox.pack(side="left", fill="x", expand=True, padx=5)
ttk.Button(eq_top_frame, text="Refresh", command=populate_audio_devices).pack(side="left", padx=5)
eq_bottom_frame = ttk.Frame(tab6, padding=5); eq_bottom_frame.pack(fill="x")
ttk.Label(eq_bottom_frame, text="Effect:").pack(side="left", padx=5); eq_effect_combobox = ttk.Combobox(eq_bottom_frame, state="readonly", values=["Classic Bars", "Radial Pulse", "Vortex"]); eq_effect_combobox.pack(side="left", fill="x", expand=True, padx=5); eq_effect_combobox.set("Classic Bars")
ttk.Button(tab6, text="START VISUALIZER", command=start_equalizer, style="Accent.TButton").pack(pady=20, ipady=10)
ttk.Label(tab6, text="This visualizer captures audio playing on your PC.\nSelect your main speakers or headphones from the list.", justify="center").pack(pady=10)

# This button is always visible at the bottom.
bottom_frame = ttk.Frame(main_frame); bottom_frame.pack(fill="x", pady=(10,0))
ttk.Button(bottom_frame, text="STOP ALL ACTIVITY", command=stop_all_activity).pack(fill="x", ipady=5)

def on_closing():
    stop_all_activity(); root.destroy()

root.protocol("WM_DELETE_WINDOW", on_closing)

populate_audio_devices()
if DEFAULT_PIXOO_IP:
    threading.Thread(target=connect_to_pixoo, args=(DEFAULT_PIXOO_IP,), daemon=True).start()

root.mainloop()