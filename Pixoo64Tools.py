#
# Pixoo 64 Advanced Tools by Doug Farmer
#
# A Python application with a graphical user interface (GUI) to control a Divoom Pixoo 64 display.
# This script allows for AI image generation, screen streaming, video playback, single image/GIF display,
# mixed-media playlists, a live system performance monitor, a powerful custom text displayer,
# a live audio visualizer, an RSS feed reader, and a live webcam viewer.
#
# Main libraries used:
# - tkinter: For the GUI components.
# - Pillow (PIL): For all image processing.
# - pixoo: For communicating with the Pixoo 64 device.
# - psutil: For fetching system CPU, RAM, and Network statistics.
# - pynvml: For fetching NVIDIA GPU statistics.
# - numpy & soundcard: For the audio visualizer.
# - opencv-python: For video file decoding and webcam support.
# - feedparser: For parsing RSS and Atom feeds.
# - requests: For making API calls to web services.
#
import logging
import time
import threading
import json
import os

# This MUST be set before cv2 is imported to prevent console spam
os.environ["OPENCV_LOG_LEVEL"] = "OFF"

import random
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
from PIL import ImageGrab, Image, ImageTk, ImageDraw, ImageFilter, ImageSequence, ImageFont
from pixoo import Pixoo
import psutil
import numpy as np
import soundcard as sc
import warnings
import cv2
import feedparser
import requests
import io
import sys
import contextlib

try:
    import pynvml
    pynvml.nvmlInit()
    NVIDIA_GPU_SUPPORT = True
except Exception:
    NVIDIA_GPU_SUPPORT = False

# Suppress a specific, harmless warning from the soundcard library
warnings.filterwarnings('ignore', category=sc.SoundcardRuntimeWarning)

# Sets up how logs are displayed
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
video_active = threading.Event()
rss_active = threading.Event()
ai_image_active = threading.Event()
webcam_active = threading.Event()
webcam_slideshow_active = threading.Event()
ALL_EVENTS = [streaming, playlist_active, gif_active, sysmon_active, text_active, equalizer_active, video_active, rss_active, ai_image_active, webcam_active, webcam_slideshow_active]

show_grid = True
resize_method = Image.Resampling.BICUBIC
last_source_image = None
playlist_files = []
rss_feed_urls = []
current_gif_path = None
current_video_path = None
text_color = (255, 255, 255)
outline_color = (0, 0, 0)
font_path = None

vortex_angle = 0
vortex_particles = []
current_webcam_frame = None
captured_frames = []


filter_options = {
    "NONE": None, "BLUR": ImageFilter.BLUR, "CONTOUR": ImageFilter.CONTOUR,
    "DETAIL": ImageFilter.DETAIL, "EDGE_ENHANCE": ImageFilter.EDGE_ENHANCE,
    "EDGE_ENHANCE_MORE": ImageFilter.EDGE_ENHANCE_MORE, "EMBOSS": ImageFilter.EMBOSS,
    "FIND_EDGES": ImageFilter.FIND_EDGES, "SHARPEN": ImageFilter.SHARPEN,
    "SMOOTH": ImageFilter.SMOOTH, "SMOOTH_MORE": ImageFilter.SMOOTH_MORE
}

# --- Configuration Management ---

def load_config():
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, 'r') as f:
            config_data = json.load(f)
            global rss_feed_urls
            rss_feed_urls = config_data.get('rss_feeds', [])
            return config_data
    return {}

def save_config(data):
    data['rss_feeds'] = rss_feed_urls
    with open(CONFIG_FILE, 'w') as f:
        json.dump(data, f, indent=4)

app_config = load_config()
DEFAULT_PIXOO_IP = app_config.get('ip_address', '')

# --- Core Functions ---

def stop_all_activity():
    if gif_active.is_set() or text_active.is_set():
        toggle_processing_controls(enabled=True)
    if webcam_active.is_set():
        webcam_capture_button.config(state="disabled")

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
# Background Tasks
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

def advanced_sysmon_task(options):
    tiny_font = ImageFont.load_default()
    last_net_io = psutil.net_io_counters()
    last_time = time.time()

    while sysmon_active.is_set():
        if pixoo is None: time.sleep(1); continue
        
        stats = {}
        if options["cpu_total"] or options["cpu_cores"]:
                stats["cpu_total"] = psutil.cpu_percent(interval=1)
                if options["cpu_cores"]:
                        stats["cpu_cores"] = psutil.cpu_percent(interval=None, percpu=True)
        else:
                time.sleep(1) 

        if options["ram"]: stats["ram"] = psutil.virtual_memory().percent
        
        if options["gpu"]:
            try:
                handle = pynvml.nvmlDeviceGetHandleByIndex(0)
                gpu_util = pynvml.nvmlDeviceGetUtilizationRates(handle).gpu
                gpu_temp = pynvml.nvmlDeviceGetTemperature(handle, pynvml.NVML_TEMPERATURE_GPU)
                stats["gpu"] = {"util": gpu_util, "temp": gpu_temp}
            except Exception as e:
                logging.warning(f"Could not get NVIDIA GPU stats: {e}")
                stats["gpu"] = None

        if options["network"]:
            current_net_io = psutil.net_io_counters()
            current_time = time.time()
            elapsed_time = current_time - last_time
            
            if elapsed_time > 0:
                upload_speed = (current_net_io.bytes_sent - last_net_io.bytes_sent) / elapsed_time / 1024
                download_speed = (current_net_io.bytes_recv - last_net_io.bytes_recv) / elapsed_time / 1024
                stats["network"] = {"up": upload_speed, "down": download_speed}
            
            last_net_io = current_net_io
            last_time = current_time

        try:
            img = Image.new('RGB', (64, 64), 'black')
            draw_sysmon_dashboard(img, stats, tiny_font)
            
            pixoo.draw_image(img); pixoo.push()
            update_preview_label(img)
        except Exception as e:
            logging.error(f"Error in system monitor: {e}"); sysmon_active.clear(); break

def format_speed(speed_in_kb):
    if speed_in_kb >= 1000:
        speed_in_mb = speed_in_kb / 1024
        return f"{speed_in_mb:.1f} MB/s"
    else:
        return f"{speed_in_kb:.0f} KB/s"

def draw_sysmon_dashboard(img, stats, font):
    draw = ImageDraw.Draw(img)
    y_offset = 2
    if "cpu_total" in stats:
        draw.text((2, y_offset), f"CPU: {stats['cpu_total']:.0f}%", font=font, fill="white")
        y_offset += 10
    if "ram" in stats:
        draw.text((2, y_offset), f"RAM: {stats['ram']:.0f}%", font=font, fill="white")
        y_offset += 10
    if stats.get("gpu"):
        draw.text((2, y_offset), f"GPU: {stats['gpu']['util']}%", font=font, fill="white")
        y_offset += 10
    if "network" in stats:
        up_text = format_speed(stats['network']['up'])
        down_text = format_speed(stats['network']['down'])
        draw.text((2, y_offset), f"UP: {up_text}", font=font, fill="white")
        y_offset += 10
        draw.text((2, y_offset), f"DN: {down_text}", font=font, fill="white")

def play_video_for_duration(video_path, duration_s):
    start_time = time.monotonic()
    
    try:
        cap = cv2.VideoCapture(video_path)
        if not cap.isOpened():
            logging.error(f"Could not open video file in playlist: {video_path}")
            playlist_active.wait(2)
            return

        fps = cap.get(cv2.CAP_PROP_FPS)
        frame_delay = 1.0 / fps if fps > 0 else 1.0 / 30.0
        next_frame_time = time.monotonic()
        
        while time.monotonic() - start_time < duration_s:
            if not playlist_active.is_set(): break

            ret, frame = cap.read()
            if not ret:
                cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                next_frame_time = time.monotonic()
                continue

            # Frame Skipping Logic
            if time.monotonic() > next_frame_time:
                next_frame_time += frame_delay
                continue

            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            pil_image = Image.fromarray(frame_rgb)
            
            processed = process_image(pil_image)
            if pixoo:
                pixoo.draw_image(processed); pixoo.push()
            update_preview_label(processed)
            
            next_frame_time += frame_delay
            sleep_duration = next_frame_time - time.monotonic()
            if sleep_duration > 0:
                time.sleep(sleep_duration)

        cap.release()
    except Exception as e:
        logging.error(f"Error during playlist video playback '{video_path}': {e}")
        playlist_active.wait(2)

def play_gif_for_duration(gif_path, duration_s):
    start_time = time.monotonic()
    
    try:
        with Image.open(gif_path) as gif:
            frames = []
            for frame_image in ImageSequence.Iterator(gif):
                frame_duration = frame_image.info.get('duration', 100) / 1000.0
                converted_frame = frame_image.convert("RGB")
                processed_frame = process_image(converted_frame)
                frames.append({'image': processed_frame, 'duration': frame_duration})

            if not frames:
                logging.warning(f"Could not load frames for GIF: {gif_path}")
                return
                
            MIN_FRAME_DELAY_S = 0.02
            next_frame_time = time.monotonic()
            
            while time.monotonic() - start_time < duration_s:
                if not playlist_active.is_set(): break
                
                for frame_data in frames:
                    if not playlist_active.is_set() or time.monotonic() - start_time >= duration_s:
                        break

                    wait_time = next_frame_time - time.monotonic()
                    if wait_time > 0: time.sleep(wait_time)

                    if pixoo is None: 
                        playlist_active.wait(0.5)
                        continue
                    
                    frame_to_show = frame_data['image']
                    pixoo.draw_image(frame_to_show); pixoo.push()
                    update_preview_label(frame_to_show)
                    
                    next_frame_time += max(frame_data['duration'], MIN_FRAME_DELAY_S)

    except Exception as e:
        logging.error(f"Could not play playlist GIF '{gif_path}': {e}")
        playlist_active.wait(2)

def playlist_task(interval_s, shuffle):
    playlist_copy = playlist_files.copy()
    if shuffle:
        random.shuffle(playlist_copy)
        logging.info("Playlist shuffled.")

    while playlist_active.is_set():
        if not playlist_copy: 
            logging.warning("Playlist is empty, stopping.")
            break
            
        for item_path in playlist_copy:
            if not playlist_active.is_set(): break
            
            file_ext = os.path.splitext(item_path)[1].lower()
            
            if file_ext == '.gif':
                logging.info(f"Playing GIF from playlist: {item_path} for {interval_s}s")
                play_gif_for_duration(item_path, interval_s)
            elif file_ext in ['.mp4', '.mkv', '.avi', '.mov']:
                logging.info(f"Playing video from playlist: {item_path} for {interval_s}s")
                play_video_for_duration(item_path, interval_s)
            else:
                logging.info(f"Displaying image from playlist: {item_path} for {interval_s}s")
                try:
                    image = Image.open(item_path).convert("RGB")
                    processed = process_image(image)
                    pixoo.draw_image(processed); pixoo.push()
                    update_preview_label(processed)
                    # Wait for the interval duration, checking the event frequently
                    for _ in range(interval_s * 4): # Check 4 times a second
                        if not playlist_active.is_set(): break 
                        time.sleep(0.25)
                except Exception as e:
                    logging.error(f"Error cycling image '{item_path}': {e}")
                    playlist_active.wait(2)
        
        if not playlist_active.is_set(): break

        if shuffle:
            random.shuffle(playlist_copy)
            logging.info("Playlist re-shuffled for next cycle.")

    logging.info("Playlist cycle finished.")

def standalone_gif_task():
    toggle_processing_controls(enabled=False)
    gif_path_label.config(text="Processing, please wait...")

    try:
        with Image.open(current_gif_path) as gif:
            frames = []
            for frame_image in ImageSequence.Iterator(gif):
                frame_duration = frame_image.info.get('duration', 100) / 1000.0
                converted_frame = frame_image.convert("RGB")
                processed_frame = process_image(converted_frame)
                frames.append({'image': processed_frame, 'duration': frame_duration})
        
        if not frames:
            messagebox.showerror("GIF Error", "Could not load any frames from the GIF.")
            gif_path_label.config(text="GIF processing failed.")
            toggle_processing_controls(enabled=True)
            gif_active.clear()
            return

        gif_path_label.config(text=f"Playing: {os.path.basename(current_gif_path)}")
        
        MIN_FRAME_DELAY_S = 0.02
        next_frame_time = time.monotonic()
        
        while gif_active.is_set():
            for frame_data in frames:
                if not gif_active.is_set(): break
                if pixoo is None: 
                    gif_active.wait(0.5)
                    continue

                wait_time = next_frame_time - time.monotonic()
                if wait_time > 0: time.sleep(wait_time)
                
                frame_image = frame_data['image']
                pixoo.draw_image(frame_image); pixoo.push()
                update_preview_label(frame_image)

                next_frame_time += max(frame_data['duration'], MIN_FRAME_DELAY_S)
            
            if not gif_active.is_set(): break

    except Exception as e:
        messagebox.showerror("GIF Error", f"Could not process or play GIF: {e}")
    finally:
        gif_path_label.config(text=f"Selected: {os.path.basename(current_gif_path)}")
        toggle_processing_controls(enabled=True)
        gif_active.clear()
        logging.info("GIF playback finished.")

def video_playback_task():
    if not current_video_path: return
    
    try:
        cap = cv2.VideoCapture(current_video_path) 
        if not cap.isOpened():
            messagebox.showerror("Video Error", "Could not open video file.")
            video_active.clear()
            return
            
        fps = cap.get(cv2.CAP_PROP_FPS)
        frame_delay = 1.0 / fps if fps > 0 else 1.0 / 30.0
        next_frame_time = time.monotonic()
        
        while video_active.is_set() and cap.isOpened():
            ret, frame = cap.read()
            if not ret:
                cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                next_frame_time = time.monotonic()
                continue
            
            # Frame Skipping Logic
            if time.monotonic() > next_frame_time:
                next_frame_time += frame_delay
                continue

            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            pil_image = Image.fromarray(frame_rgb)
            
            processed = process_image(pil_image)
            if pixoo:
                pixoo.draw_image(processed)
                pixoo.push()
            update_preview_label(processed)
            
            next_frame_time += frame_delay
            sleep_duration = next_frame_time - time.monotonic()
            if sleep_duration > 0:
                time.sleep(sleep_duration)

        cap.release()
    except Exception as e:
        logging.error(f"Error during video playback: {e}")
        messagebox.showerror("Video Error", f"An error occurred during playback: {e}")
    
    video_active.clear()
    logging.info("Video playback finished.")

def text_wrap(text, font, max_width):
    lines = []
    words = text.split()
    
    if not words:
        return ""

    current_line = words[0]
    for word in words[1:]:
        if font.getbbox(current_line + " " + word)[2] <= max_width:
            current_line += " " + word
        else:
            lines.append(current_line)
            current_line = word
    lines.append(current_line)
    
    return "\n".join(lines)

def scrolling_text_task(text_to_scroll, font_size, delay_ms, active_event):
    try:
        font = ImageFont.load_default()
        custom_font_path = font_path
        if custom_font_path:
            try: 
                font = ImageFont.truetype(custom_font_path, font_size)
            except IOError: 
                logging.warning(f"Could not load font: {custom_font_path}. Using default.")
        
        while active_event.is_set():
            temp_draw = ImageDraw.Draw(Image.new('RGB', (0,0)))
            left, top, right, bottom = temp_draw.textbbox((0,0), text_to_scroll, font=font)
            text_width, text_height = right - left, bottom - top

            x_pos = (64 - text_width) // 2 

            full_text_image = Image.new('RGBA', (text_width, text_height))
            draw = ImageDraw.Draw(full_text_image)
            draw.text((-left, -top), text_to_scroll, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
            
            y = 64
            while active_event.is_set():
                frame = Image.new('RGB', (64, 64), (0,0,0))
                frame.paste(full_text_image, (x_pos, y), full_text_image) 
                if pixoo: pixoo.draw_image(frame); pixoo.push()
                update_preview_label(frame)
                
                y -= 1
                if y < -text_height:
                    break
                
                active_event.wait(delay_ms / 1000.0)

            if active_event == rss_active:
                break 

    except Exception as e:
        logging.error(f"Error during scrolling text task: {e}")
    
    if active_event == text_active:
        toggle_processing_controls(enabled=True)


def rss_task(delay_between_headlines, scroll_speed_ms):
    try:
        rss_font_size = 12
        rss_font = ImageFont.load_default()
        if font_path:
            try: 
                rss_font = ImageFont.truetype(font_path, rss_font_size)
            except IOError: 
                logging.warning(f"Could not load custom font for RSS. Using default.")
    except Exception as e:
        logging.error(f"Failed to load font for RSS task: {e}")
        rss_font = ImageFont.load_default()

    while rss_active.is_set():
        if not rss_feed_urls:
            logging.warning("RSS feed list is empty, stopping.")
            messagebox.showwarning("Empty", "Your RSS feed list is empty.")
            break

        logging.info("Starting new RSS feed cycle.")
        for url in rss_feed_urls:
            if not rss_active.is_set(): break
            
            logging.info(f"Fetching RSS feed: {url}")
            try:
                feed = feedparser.parse(url, agent="Pixoo64AdvancedTools/1.0")
                if feed.bozo:
                    logging.warning(f"Feed may be malformed: {url}, Bozo reason: {feed.bozo_exception}")

                for entry in feed.entries:
                    if not rss_active.is_set(): break
                    
                    headline = entry.title
                    wrapped_headline = text_wrap(headline, rss_font, 64)
                    logging.info(f"Displaying headline: {headline}")
                    scrolling_text_task(wrapped_headline, rss_font_size, scroll_speed_ms, rss_active)
                    
                    if rss_active.is_set():
                        rss_active.wait(delay_between_headlines)

            except Exception as e:
                logging.error(f"Failed to fetch or parse RSS feed {url}: {e}")
                if rss_active.is_set():
                    rss_active.wait(5)
        
        logging.info("Finished RSS feed cycle.")
        if rss_active.is_set():
                rss_active.wait(60)

    logging.info("RSS Feed task stopped.")


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

def ai_image_generation_task(prompt, use_pixel_style, use_hd):
    ai_image_active.set()
    ai_status_label.config(text="Status: Generating...")
    
    try:
        base_url = "https://image.pollinations.ai/prompt/"
        
        final_prompt = prompt
        if use_pixel_style:
            final_prompt += ", pixel art, 8-bit, sprite"
        if use_hd:
            final_prompt += ", 4k, ultra detailed"
            
        encoded_prompt = requests.utils.quote(final_prompt)
        
        full_url = f"{base_url}{encoded_prompt}"
        logging.info(f"Requesting AI image from URL: {full_url}")
        
        response = requests.get(full_url, timeout=90)
        
        if response.status_code == 200:
            image_data = response.content
            ai_image = Image.open(io.BytesIO(image_data))
            
            processed = process_image(ai_image)
            if pixoo:
                pixoo.draw_image(processed)
                pixoo.push()
            update_preview_label(processed)
            ai_status_label.config(text="Status: Done!")
        else:
            messagebox.showerror("API Error", f"Failed to generate image. Status code: {response.status_code}\n{response.text}")
            ai_status_label.config(text="Status: Error")

    except requests.exceptions.RequestException as e:
        messagebox.showerror("Network Error", f"Could not connect to the image generation service: {e}")
        ai_status_label.config(text="Status: Network Error")
    except Exception as e:
        logging.error(f"Error during AI image generation: {e}")
        messagebox.showerror("Error", f"An unexpected error occurred: {e}")
        ai_status_label.config(text="Status: Error")
    finally:
        ai_image_active.clear()


def webcam_slideshow_task(interval_s, shuffle):
    while webcam_slideshow_active.is_set():
        if not captured_frames:
            logging.info("Webcam slideshow stopped: no frames to display.")
            break

        frames_to_play = captured_frames.copy()
        if shuffle:
            random.shuffle(frames_to_play)

        for frame_image in frames_to_play:
            if not webcam_slideshow_active.is_set(): break

            processed = process_image(frame_image)
            if pixoo:
                pixoo.draw_image(processed)
                pixoo.push()
            update_preview_label(processed)
            
            # Use the same robust timing logic as the image playlist
            for _ in range(interval_s):
                if not webcam_slideshow_active.is_set(): break 
                time.sleep(1)
        
        if not webcam_slideshow_active.is_set(): break
    
    logging.info("Webcam slideshow finished.")


#
# GUI Actions
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

def start_advanced_sysmon():
    stop_all_activity()
    options = {
        "cpu_total": cpu_total_var.get(),
        "ram": ram_var.get(),
        "gpu": gpu_var.get(),
        "network": network_var.get(),
        "cpu_cores": cpu_cores_var.get()
    }
    if not any(options.values()):
        messagebox.showwarning("No Selection", "Please select at least one metric to monitor.")
        return
    
    if options["gpu"] and not NVIDIA_GPU_SUPPORT:
        messagebox.showerror("GPU Error", "NVIDIA drivers and the pynvml library are required for GPU monitoring.")
        gpu_var.set(False)
        return

    sysmon_active.set()
    threading.Thread(target=advanced_sysmon_task, args=(options,), daemon=True).start()

def browse_image():
    stop_all_activity(); path = filedialog.askopenfilename(filetypes=[("Images", "*.png;*.jpg;*.jpeg;*.bmp")])
    if not path: return
    try: 
        image = Image.open(path).convert("RGB"); processed = process_image(image)
        if pixoo: pixoo.draw_image(processed); pixoo.push()
        update_preview_label(processed)
    except Exception as e: messagebox.showerror("Error", f"Failed to process image: {e}")

def browse_gif():
    global current_gif_path; stop_all_activity(); path = filedialog.askopenfilename(filetypes=[("GIFs", "*.gif")])
    if not path: return
    current_gif_path = path; gif_path_label.config(text=f"Selected: {os.path.basename(path)}")
    try:
        with Image.open(path) as gif: 
            preview_frame = gif.convert("RGB")
            processed = process_image(preview_frame)
            update_preview_label(processed)
    except Exception as e: messagebox.showerror("Error", f"Failed to load GIF preview: {e}")

def browse_video():
    global current_video_path
    stop_all_activity()
    path = filedialog.askopenfilename(filetypes=[("Video Files", "*.mp4 *.mkv *.avi *.mov")])
    if not path: return
    current_video_path = path
    video_path_label.config(text=f"Selected: {os.path.basename(path)}")
    try:
        cap = cv2.VideoCapture(path)
        ret, frame = cap.read()
        if ret:
            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            pil_image = Image.fromarray(frame_rgb)
            processed = process_image(pil_image)
            update_preview_label(processed)
        cap.release()
    except Exception as e:
        logging.error(f"Failed to load video preview: {e}")

def start_video():
    stop_all_activity()
    if not current_video_path:
        messagebox.showerror("Error", "No video file selected.")
        return
    video_active.set()
    threading.Thread(target=video_playback_task, daemon=True).start()

def start_gif():
    stop_all_activity()
    if not current_gif_path: messagebox.showerror("Error", "No GIF file loaded."); return
    gif_active.set()
    # This now calls the new unified task directly
    threading.Thread(target=standalone_gif_task, daemon=True).start()

def start_playlist():
    stop_all_activity();
    if not playlist_files: messagebox.showwarning("Empty", "Playlist is empty."); return
    try:
        interval_value = int(interval_spinbox.get());
        if interval_value < 1: interval_value = 5
    except (ValueError, tk.TclError): interval_value = 5
    
    shuffle = shuffle_playlist_var.get()
    playlist_active.set()
    threading.Thread(target=playlist_task, args=(interval_value, shuffle), daemon=True).start()

def add_to_playlist():
    # Updated to accept all supported media types in one go
    files = filedialog.askopenfilenames(
        title="Add Media to Playlist",
        filetypes=[
            ("All Supported Media", "*.png *.jpg *.jpeg *.bmp *.gif *.mp4 *.mkv *.avi *.mov"),
            ("Image Files", "*.png *.jpg *.jpeg *.bmp"), 
            ("Animated GIFs", "*.gif"),
            ("Video Files", "*.mp4 *.mkv *.avi *.mov")
        ]
    )
    for f in files:
        if f not in playlist_files: playlist_files.append(f); playlist_listbox.insert(tk.END, os.path.basename(f))

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
                if file_path: playlist_files.append(file_path); playlist_listbox.insert(tk.END, os.path.basename(file_path))
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
    if path: 
        font_path = path
        font_path_label.config(text=f"Font: {os.path.basename(path)}")
        update_text_preview()

def reset_to_default_font():
    global font_path
    font_path = None
    font_path_label.config(text="Font: Default")
    update_text_preview()

def display_text():
    stop_all_activity()
    if pixoo is None: messagebox.showerror("Error", "Not connected to Pixoo."); return
    text = text_entry.get("1.0", "end-1c")
    if not text: 
        if pixoo: pixoo.clear(); pixoo.push()
        update_preview_label(Image.new('RGB', (64,64), (0,0,0)))
        return
        
    font_size, x_pos, y_pos, delay_ms = int(font_size_spinbox.get()), int(pos_x_spinbox.get()), int(pos_y_spinbox.get()), int(anim_speed_spinbox.get())
    is_scrolling = scroll_text_var.get()
    
    if not is_scrolling:
        font = ImageFont.load_default()
        if font_path:
            try: font = ImageFont.truetype(font_path, font_size)
            except IOError: messagebox.showwarning("Font Error", f"Could not load font. Using default.")
        
        img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
        draw.text((x_pos, y_pos), text, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
        if pixoo: pixoo.draw_image(img); pixoo.push()
        update_preview_label(img)
    else:
        toggle_processing_controls(enabled=False)
        text_active.set()
        threading.Thread(target=scrolling_text_task, args=(text, font_size, delay_ms, text_active), daemon=True).start()

def populate_audio_devices():
    device_listbox.set(''); device_listbox['values'] = []
    try:
        speakers = sc.all_speakers(); loopbacks = sc.all_microphones(include_loopback=True)
        device_names = [d.name for d in speakers] + [d.name for d in loopbacks if d.isloopback]
        device_listbox['values'] = sorted(list(set(device_names)))
        if device_listbox['values']: device_listbox.set(device_listbox['values'][0])
    except Exception as e:
        logging.error(f"Could not get audio devices: {e}")
        messagebox.showerror("Audio Error", "Could not find any audio devices.")

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

def add_rss_feed():
    url = rss_url_entry.get().strip()
    if not url: return
    if url in rss_feed_urls:
        messagebox.showinfo("Duplicate", "This feed URL is already in the list.")
        return
    
    rss_feed_urls.append(url)
    rss_listbox.insert(tk.END, url)
    rss_url_entry.delete(0, tk.END)
    save_config(app_config)

def remove_rss_feed():
    indices = sorted(rss_listbox.curselection(), reverse=True)
    if not indices: return
    for i in indices:
        rss_listbox.delete(i)
        rss_feed_urls.pop(i)
    save_config(app_config)

def start_rss_feed():
    stop_all_activity()
    if not rss_feed_urls:
        messagebox.showwarning("Empty", "Please add at least one RSS feed URL.")
        return
    
    delay = int(rss_delay_spinbox.get())
    speed = int(rss_speed_spinbox.get())

    rss_active.set()
    threading.Thread(target=rss_task, args=(delay, speed), daemon=True).start()

def start_ai_image_generation():
    stop_all_activity()
    prompt = ai_prompt_entry.get("1.0", "end-1c").strip()
    if not prompt:
        messagebox.showwarning("Empty Prompt", "Please enter a description for the image.")
        return
    
    if ai_image_active.is_set():
        messagebox.showinfo("In Progress", "An image is already being generated.")
        return
    
    use_pixel = pixel_style_var.get()
    use_hd = hd_style_var.get()
    
    threading.Thread(target=ai_image_generation_task, args=(prompt, use_pixel, use_hd), daemon=True).start()

def save_ai_image():
    if last_source_image is None:
        messagebox.showinfo("No Image", "Please generate an image first before saving.")
        return
    
    path = filedialog.asksaveasfilename(
        defaultextension=".png",
        filetypes=[("PNG files", "*.png"), ("All files", "*.*")],
        title="Save AI Image As"
    )
    if not path:
        return
        
    try:
        last_source_image.save(path, "PNG")
        messagebox.showinfo("Success", f"Image saved successfully to:\n{path}")
    except Exception as e:
        messagebox.showerror("Save Error", f"Failed to save image: {e}")

def discover_webcams_task():
    webcam_refresh_button.config(text="Scanning...", state="disabled")
    
    available_cams = []
    # Using CAP_DSHOW is good practice on Windows. The os.environ call at the
    # top of the script now handles the error message suppression.
    for i in range(10):
        cap = cv2.VideoCapture(i, cv2.CAP_DSHOW)
        if cap.isOpened():
            available_cams.append(f"Camera {i}")
            cap.release()
            
    if not available_cams:
        webcam_device_combobox['values'] = ["No webcams found"]
        webcam_device_combobox.set("No webcams found")
    else:
        webcam_device_combobox['values'] = available_cams
        webcam_device_combobox.set(available_cams[0])
        
    webcam_refresh_button.config(text="Find Webcams", state="normal")

def start_webcam_discovery():
    threading.Thread(target=discover_webcams_task, daemon=True).start()

def webcam_task(device_index):
    global current_webcam_frame
    try:
        cap = cv2.VideoCapture(device_index)
        if not cap.isOpened():
            messagebox.showerror("Webcam Error", f"Could not open Camera {device_index}.")
            webcam_active.clear()
            return
        
        webcam_capture_button.config(state="normal")
        
        while webcam_active.is_set():
            ret, frame = cap.read()
            if not ret:
                logging.warning(f"Could not read frame from Camera {device_index}.")
                time.sleep(0.1)
                continue

            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            current_webcam_frame = Image.fromarray(frame_rgb)
            
            processed = process_image(current_webcam_frame)
            if pixoo:
                pixoo.draw_image(processed); pixoo.push()
            update_preview_label(processed)
            time.sleep(1/60)
            
        cap.release()
    except Exception as e:
        logging.error(f"Error during webcam feed: {e}")
        messagebox.showerror("Webcam Error", f"An error occurred with the webcam feed: {e}")
    finally:
        webcam_active.clear()
        webcam_capture_button.config(state="disabled")

def start_webcam():
    stop_all_activity()
    
    selection = webcam_device_combobox.get()
    if not selection or "No webcams found" in selection:
        messagebox.showerror("No Webcam", "No webcam selected or found.")
        return
        
    try:
        device_index = int(selection.split()[-1])
    except (ValueError, IndexError):
        messagebox.showerror("Selection Error", "Invalid webcam selection.")
        return
        
    webcam_active.set()
    threading.Thread(target=webcam_task, args=(device_index,), daemon=True).start()

def capture_webcam_frame():
    if current_webcam_frame:
        captured_frames.append(current_webcam_frame.copy())
        timestamp = time.strftime("%H:%M:%S")
        webcam_listbox.insert(tk.END, f"Frame captured at {timestamp}")
        webcam_listbox.see(tk.END)

def display_captured_frame():
    selection_indices = webcam_listbox.curselection()
    if not selection_indices:
        return
    
    selected_index = selection_indices[0]
    
    if 0 <= selected_index < len(captured_frames):
        stop_all_activity()
        image_to_display = captured_frames[selected_index]
        processed = process_image(image_to_display)
        if pixoo:
            pixoo.draw_image(processed)
            pixoo.push()
        update_preview_label(processed)

def remove_captured_frame():
    indices = sorted(webcam_listbox.curselection(), reverse=True)
    if not indices: return
    for i in indices:
        webcam_listbox.delete(i)
        captured_frames.pop(i)

def export_captured_frames():
    if not captured_frames:
        messagebox.showinfo("No Frames", "There are no captured frames to export.")
        return
    
    directory = filedialog.askdirectory(title="Select Folder to Save Frames")
    if not directory:
        return
        
    try:
        for i, frame_image in enumerate(captured_frames):
            filename = f"captured_frame_{i+1}_{int(time.time())}.png"
            save_path = os.path.join(directory, filename)
            frame_image.save(save_path, "PNG")
        messagebox.showinfo("Success", f"Successfully exported {len(captured_frames)} frames to:\n{directory}")
    except Exception as e:
        messagebox.showerror("Export Error", f"Failed to export frames: {e}")

def import_captured_frames():
    paths = filedialog.askopenfilenames(
        title="Select Image Frames to Import",
        filetypes=[("Image Files", "*.png *.jpg *.jpeg *.bmp"), ("All files", "*.*")]
    )
    if not paths:
        return
        
    for path in paths:
        try:
            image = Image.open(path).convert("RGB")
            captured_frames.append(image)
            webcam_listbox.insert(tk.END, f"Imported: {os.path.basename(path)}")
        except Exception as e:
            logging.error(f"Failed to import image {path}: {e}")
            messagebox.showwarning("Import Error", f"Could not import file:\n{path}")
    webcam_listbox.see(tk.END)

def start_webcam_slideshow():
    stop_all_activity()
    if not captured_frames:
        messagebox.showwarning("No Frames", "There are no captured frames to play in a slideshow.")
        return
        
    try:
        interval = int(webcam_interval_spinbox.get())
    except ValueError:
        interval = 5

    shuffle = webcam_shuffle_var.get()
    webcam_slideshow_active.set()
    threading.Thread(target=webcam_slideshow_task, args=(interval, shuffle), daemon=True).start()

#
# GUI Setup
#

root = tk.Tk(); root.title("Pixoo 64 Advanced Tools"); style = ttk.Style(root)
main_frame = ttk.Frame(root, padding=10); main_frame.pack(fill="both", expand=True)

ip_frame = ttk.Frame(main_frame); ip_frame.pack(fill="x", pady=(0, 10))
ttk.Label(ip_frame, text="Pixoo IP:").pack(side=tk.LEFT); ip_entry = ttk.Entry(ip_frame); ip_entry.pack(side=tk.LEFT, fill="x", expand=True, padx=5); ip_entry.insert(0, DEFAULT_PIXOO_IP)
connect_button = ttk.Button(ip_frame, text="Connect", command=on_connect_button_click); connect_button.pack(side=tk.LEFT)

notebook = ttk.Notebook(main_frame); notebook.pack(fill="both", expand=True, pady=5)

# Create all tab frames
tab1 = ttk.Frame(notebook, padding=10)
tab7 = ttk.Frame(notebook, padding=10)
tab2 = ttk.Frame(notebook, padding=10)
tab5 = ttk.Frame(notebook, padding=10)
tab10 = ttk.Frame(notebook, padding=10) 
tab6 = ttk.Frame(notebook, padding=10)
tab3 = ttk.Frame(notebook, padding=10)
tab8 = ttk.Frame(notebook, padding=10)
tab9 = ttk.Frame(notebook, padding=10) 
tab4 = ttk.Frame(notebook, padding=10)

# Add tabs to notebook in the correct order
notebook.add(tab1, text='Image & Stream')
notebook.add(tab7, text='Video Player')
notebook.add(tab2, text='Playlist')
notebook.add(tab5, text='Text Display')
notebook.add(tab10, text='Webcam')
notebook.add(tab6, text='Equalizer')
notebook.add(tab3, text='System Monitor')
notebook.add(tab8, text='RSS Feeds')
notebook.add(tab9, text='AI Image Gen')
notebook.add(tab4, text='Credits')


# --- Populate Tabs ---

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
shuffle_playlist_var = tk.BooleanVar(value=False); ttk.Checkbutton(t2_right, text="Shuffle Playlist", variable=shuffle_playlist_var).pack(pady=5)
ttk.Button(t2_right, text="START PLAYLIST", command=start_playlist, style="Accent.TButton").pack(fill="x", pady=(10,2)); style.configure("Accent.TButton", foreground="green")

# Tab 3: System Monitor
sm_options_frame = ttk.LabelFrame(tab3, text="Metrics to Display (Dashboard Style)", padding=10)
sm_options_frame.pack(fill="x")
cpu_total_var = tk.BooleanVar(value=True)
ram_var = tk.BooleanVar(value=True)
gpu_var = tk.BooleanVar(value=NVIDIA_GPU_SUPPORT)
network_var = tk.BooleanVar(value=False)
cpu_cores_var = tk.BooleanVar(value=False)
ttk.Checkbutton(sm_options_frame, text="CPU (Total %)", variable=cpu_total_var).pack(anchor="w")
ttk.Checkbutton(sm_options_frame, text="RAM (%)", variable=ram_var).pack(anchor="w")
gpu_cb = ttk.Checkbutton(sm_options_frame, text="GPU (NVIDIA)", variable=gpu_var)
gpu_cb.pack(anchor="w")
if not NVIDIA_GPU_SUPPORT:
    gpu_cb.config(state="disabled")
ttk.Checkbutton(sm_options_frame, text="Network (KB/s)", variable=network_var).pack(anchor="w")
ttk.Button(tab3, text="START MONITOR", command=start_advanced_sysmon, style="Accent.TButton").pack(pady=20, ipady=10)

# Tab 4: Credits
credits_center_frame = ttk.Frame(tab4); credits_center_frame.pack(expand=True)
title_font = ("Segoe UI", 18, "bold"); author_font = ("Segoe UI", 12, "italic"); header_font = ("Segoe UI", 11, "bold"); body_font = ("Segoe UI", 10); link_font = ("Segoe UI", 10, "underline")
ttk.Label(credits_center_frame, text="Pixoo 64 Advanced Tools", font=title_font).pack(pady=(10, 0))
ttk.Label(credits_center_frame, text="by Doug Farmer", font=author_font).pack()
ttk.Label(credits_center_frame, text="Version 2.0", font=author_font).pack(pady=(0, 10))
discord_frame = ttk.Frame(credits_center_frame); discord_frame.pack(pady=5); ttk.Label(discord_frame, text="Discord:", font=body_font).pack(side=tk.LEFT); ttk.Label(discord_frame, text="wtfyd", font=link_font, foreground="#5865F2").pack(side=tk.LEFT)
ttk.Separator(credits_center_frame, orient='horizontal').pack(fill='x', padx=20, pady=20); ttk.Label(credits_center_frame, text="Special Thanks", font=header_font).pack()
ttk.Label(credits_center_frame, text="All credit for the foundational concept and starting point goes to MikeTheTech. This tool was built and expanded upon his great work.", font=body_font, wraplength=400, justify="center").pack(pady=5)
ttk.Separator(credits_center_frame, orient='horizontal').pack(fill='x', padx=20, pady=20); ttk.Label(credits_center_frame, text="https://github.com/tidyhf/Pixoo64-Advanced-Tools", font=author_font).pack(pady=10)

# Tab 5: Text Display
t5_left = ttk.Frame(tab5); t5_left.pack(side=tk.LEFT, fill="both", expand=True, padx=(0,10)); t5_right = ttk.Frame(tab5); t5_right.pack(side=tk.LEFT, fill="y")
text_entry_frame = ttk.LabelFrame(t5_left, text="Message", padding=5); text_entry_frame.pack(fill="both", expand=True); text_entry = tk.Text(text_entry_frame, height=5, wrap="word"); text_entry.pack(fill="both", expand=True); text_entry.bind("<KeyRelease>", update_text_preview)
font_frame = ttk.LabelFrame(t5_left, text="Font & Style", padding=5); font_frame.pack(fill="x", pady=5)
font_buttons_frame = ttk.Frame(font_frame); font_buttons_frame.pack(fill="x")
ttk.Button(font_buttons_frame, text="Browse for Font File (.ttf)", command=browse_for_font).pack(side="left", fill="x", expand=True)
ttk.Button(font_buttons_frame, text="Reset to Default", command=reset_to_default_font).pack(side="left", padx=(5,0))
font_path_label = ttk.Label(font_frame, text="Font: Default"); font_path_label.pack(anchor="w", pady=2)
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

# Tab 7: Video Player
video_browse_frame = ttk.LabelFrame(tab7, text="Video File", padding=10)
video_browse_frame.pack(fill="x")
video_path_label = ttk.Label(video_browse_frame, text="No video selected.")
video_path_label.pack(fill="x", pady=5)
ttk.Button(video_browse_frame, text="Browse for Video File", command=browse_video).pack(fill="x")
video_controls_frame = ttk.Frame(tab7, padding=10)
video_controls_frame.pack(fill="x", pady=10)
ttk.Button(video_controls_frame, text="PLAY VIDEO", command=start_video, style="Accent.TButton").pack(fill="x", ipady=10)
ttk.Label(tab7, text="Supports most common video formats (mp4, mkv, avi, mov).\nVideo will loop automatically.", justify="center").pack(pady=10)

# Tab 8: RSS Feeds
rss_main_frame = ttk.Frame(tab8, padding=5)
rss_main_frame.pack(fill="both", expand=True)
rss_left_frame = ttk.Frame(rss_main_frame); rss_left_frame.pack(side=tk.LEFT, fill="both", expand=True, padx=(0, 10))
rss_right_frame = ttk.Frame(rss_main_frame); rss_right_frame.pack(side=tk.RIGHT, fill="y")
url_frame = ttk.LabelFrame(rss_left_frame, text="Add New RSS Feed URL", padding=5)
url_frame.pack(fill="x")
rss_url_entry = ttk.Entry(url_frame)
rss_url_entry.pack(side="left", fill="x", expand=True, padx=(0, 5))
ttk.Button(url_frame, text="Add", command=add_rss_feed).pack(side="left")
list_frame = ttk.LabelFrame(rss_left_frame, text="Your Feeds", padding=5)
list_frame.pack(fill="both", expand=True, pady=10)
rss_scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
rss_listbox = tk.Listbox(list_frame, yscrollcommand=rss_scrollbar.set)
rss_scrollbar.config(command=rss_listbox.yview)
rss_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
rss_listbox.pack(side=tk.LEFT, fill="both", expand=True)
for url in rss_feed_urls:
    rss_listbox.insert(tk.END, url)
ttk.Button(rss_right_frame, text="Remove Selected", command=remove_rss_feed).pack(fill="x", pady=2)
ttk.Separator(rss_right_frame).pack(fill="x", pady=10)
settings_frame = ttk.LabelFrame(rss_right_frame, text="Settings", padding=5)
settings_frame.pack(fill="x")
ttk.Label(settings_frame, text="Delay Per Headline (s):").pack()
rss_delay_spinbox = tk.Spinbox(settings_frame, from_=1, to=300, width=10, justify=tk.CENTER)
rss_delay_spinbox.pack(fill="x", pady=2)
rss_delay_spinbox.delete(0, "end"); rss_delay_spinbox.insert(0, "5")
ttk.Label(settings_frame, text="Scroll Speed (ms):").pack()
rss_speed_spinbox = tk.Spinbox(settings_frame, from_=10, to=1000, increment=10, width=10, justify=tk.CENTER)
rss_speed_spinbox.pack(fill="x", pady=2)
rss_speed_spinbox.delete(0, "end"); rss_speed_spinbox.insert(0, "35")
ttk.Button(rss_right_frame, text="START RSS FEED", command=start_rss_feed, style="Accent.TButton").pack(fill="x", pady=(10,2), ipady=5)

# Tab 9: AI Image Generation
ai_main_frame = ttk.Frame(tab9, padding=5)
ai_main_frame.pack(fill="both", expand=True)
ai_prompt_frame = ttk.LabelFrame(ai_main_frame, text="Image Description Prompt", padding=5)
ai_prompt_frame.pack(fill="x")
ai_prompt_entry = tk.Text(ai_prompt_frame, height=4, wrap="word")
ai_prompt_entry.pack(fill="x", expand=True)
ai_options_frame = ttk.LabelFrame(ai_main_frame, text="Generation Options", padding=5)
ai_options_frame.pack(fill="x", pady=5)
pixel_style_var = tk.BooleanVar(value=True)
hd_style_var = tk.BooleanVar(value=False)
ttk.Checkbutton(ai_options_frame, text="Pixel Art Style (Recommended)", variable=pixel_style_var).pack(anchor="w")
ttk.Checkbutton(ai_options_frame, text="HD Quality (Slower, uses more keywords)", variable=hd_style_var).pack(anchor="w")
ai_status_label = ttk.Label(ai_main_frame, text="Status: Ready")
ai_status_label.pack(pady=5)
ai_btn_frame = ttk.Frame(ai_main_frame)
ai_btn_frame.pack(fill="x", pady=5)
ttk.Button(ai_btn_frame, text="GENERATE IMAGE", command=start_ai_image_generation, style="Accent.TButton").pack(side="left", fill="x", expand=True)
ttk.Button(ai_btn_frame, text="Save Last Image", command=save_ai_image).pack(side="left", fill="x", expand=True, padx=(5,0))
ttk.Label(ai_main_frame, text="Powered by Pollinations.ai", justify="center").pack(pady=5)

# Tab 10: Webcam
webcam_main_frame = ttk.Frame(tab10, padding=5)
webcam_main_frame.pack(fill="both", expand=True)
webcam_left_frame = ttk.Frame(webcam_main_frame); webcam_left_frame.pack(side=tk.LEFT, fill="y", padx=(0, 10))
webcam_right_frame = ttk.Frame(webcam_main_frame); webcam_right_frame.pack(side=tk.LEFT, fill="both", expand=True)
# Left side
device_frame = ttk.LabelFrame(webcam_left_frame, text="Live Controls", padding=5)
device_frame.pack(fill="x")
webcam_device_combobox = ttk.Combobox(device_frame, state="readonly", width=30)
webcam_device_combobox.pack(pady=5)
webcam_device_combobox.set("No webcams found")
webcam_refresh_button = ttk.Button(device_frame, text="Find Webcams", command=start_webcam_discovery)
webcam_refresh_button.pack(fill="x", pady=5)
ttk.Button(device_frame, text="START WEBCAM", command=start_webcam, style="Accent.TButton").pack(fill="x", ipady=5, pady=5)
webcam_capture_button = ttk.Button(device_frame, text="Capture Frame", command=capture_webcam_frame, state="disabled")
webcam_capture_button.pack(fill="x", pady=5)
# Right side: Captured frames and slideshow
capture_frame = ttk.LabelFrame(webcam_right_frame, text="Captured Frames", padding=5)
capture_frame.pack(fill="both", expand=True)
webcam_listbox_frame = ttk.Frame(capture_frame)
webcam_listbox_frame.pack(fill="both", expand=True, pady=5)
webcam_scrollbar = ttk.Scrollbar(webcam_listbox_frame, orient=tk.VERTICAL)
webcam_listbox = tk.Listbox(webcam_listbox_frame, yscrollcommand=webcam_scrollbar.set)
webcam_scrollbar.config(command=webcam_listbox.yview)
webcam_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
webcam_listbox.pack(side=tk.LEFT, fill="both", expand=True)
# Frame management buttons
frame_mgmt_frame = ttk.Frame(capture_frame)
frame_mgmt_frame.pack(fill="x", pady=(5,0))
ttk.Button(frame_mgmt_frame, text="Import", command=import_captured_frames).pack(side="left", fill="x", expand=True)
ttk.Button(frame_mgmt_frame, text="Export All", command=export_captured_frames).pack(side="left", fill="x", expand=True, padx=5)
ttk.Button(frame_mgmt_frame, text="Remove", command=remove_captured_frame).pack(side="left", fill="x", expand=True)
# Slideshow controls
slideshow_frame = ttk.LabelFrame(capture_frame, text="Slideshow", padding=5)
slideshow_frame.pack(fill="x", pady=10)
ttk.Button(slideshow_frame, text="Display Selected", command=display_captured_frame).pack(side="left", fill="x", expand=True)
ttk.Separator(slideshow_frame, orient="vertical").pack(side="left", fill="y", padx=10, pady=5)
ttk.Label(slideshow_frame, text="Interval (s):").pack(side="left")
webcam_interval_spinbox = tk.Spinbox(slideshow_frame, from_=1, to=3600, width=5, justify=tk.CENTER)
webcam_interval_spinbox.pack(side="left", padx=5)
webcam_interval_spinbox.delete(0, "end"); webcam_interval_spinbox.insert(0, "5")
webcam_shuffle_var = tk.BooleanVar(value=False)
ttk.Checkbutton(slideshow_frame, text="Shuffle", variable=webcam_shuffle_var).pack(side="left", padx=5)
ttk.Button(slideshow_frame, text="Start Slideshow", command=start_webcam_slideshow).pack(side="left", padx=5)


# This button is always visible at the bottom.
bottom_frame = ttk.Frame(main_frame); bottom_frame.pack(fill="x", pady=(10,0))
ttk.Button(bottom_frame, text="STOP ALL ACTIVITY", command=stop_all_activity).pack(fill="x", ipady=5)

def on_closing():
    stop_all_activity()
    if NVIDIA_GPU_SUPPORT:
        pynvml.nvmlShutdown()
    root.destroy()

root.protocol("WM_DELETE_WINDOW", on_closing)

# Initial population of devices
populate_audio_devices()
start_webcam_discovery()
if DEFAULT_PIXOO_IP:
    threading.Thread(target=connect_to_pixoo, args=(DEFAULT_PIXOO_IP,), daemon=True).start()

root.mainloop()