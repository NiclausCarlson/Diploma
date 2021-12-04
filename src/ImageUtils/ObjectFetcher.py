import numpy
from PIL import Image
import matplotlib.pyplot as plt
import torchvision.transforms as T
import torchvision
import numpy as np
import cv2
import random


# ade20k
class ObjectFetcher:
    COCO_INSTANCE_CATEGORY_NAMES = [
        '__background__', 'person', 'bicycle', 'car', 'motorcycle', 'airplane', 'bus',
        'train', 'truck', 'boat', 'traffic light', 'fire hydrant', 'N/A', 'stop sign',
        'parking meter', 'bench', 'bird', 'cat', 'dog', 'horse', 'sheep', 'cow',
        'elephant', 'bear', 'zebra', 'giraffe', 'N/A', 'backpack', 'umbrella', 'N/A', 'N/A',
        'handbag', 'tie', 'suitcase', 'frisbee', 'skis', 'snowboard', 'sports ball',
        'kite', 'baseball bat', 'baseball glove', 'skateboard', 'surfboard', 'tennis racket',
        'bottle', 'N/A', 'wine glass', 'cup', 'fork', 'knife', 'spoon', 'bowl',
        'banana', 'apple', 'sandwich', 'orange', 'broccoli', 'carrot', 'hot dog', 'pizza',
        'donut', 'cake', 'chair', 'couch', 'potted plant', 'bed', 'N/A', 'dining table',
        'N/A', 'N/A', 'toilet', 'N/A', 'tv', 'laptop', 'mouse', 'remote', 'keyboard', 'cell phone',
        'microwave', 'oven', 'toaster', 'sink', 'refrigerator', 'N/A', 'book',
        'clock', 'vase', 'scissors', 'teddy bear', 'hair drier', 'toothbrush'
    ]

    def __init__(self):
        self.model = torchvision.models.detection.maskrcnn_resnet50_fpn(pretrained=True)
        self.model.eval()

    def _get_prediction(self, img, threshold):
        transform = T.Compose([T.ToTensor()])
        img = transform(img)
        pred = self.model([img])
        pred_score = list(pred[0]['scores'].detach().numpy())
        pred_list = [pred_score.index(x) for x in pred_score if x > threshold]
        if len(pred_list) == 0:
            pred_t = 0
        else:
            pred_t = pred_list[-1]
        masks = (pred[0]['masks'] > 0.5).squeeze().detach().cpu().numpy()
        pred_class = [self.COCO_INSTANCE_CATEGORY_NAMES[i] for i in list(pred[0]['labels'].numpy())]
        pred_boxes = [[(i[0], i[1]), (i[2], i[3])] for i in list(pred[0]['boxes'].detach().numpy())]
        masks = masks[:pred_t + 1]
        pred_boxes = pred_boxes[:pred_t + 1]
        pred_class = pred_class[:pred_t + 1]
        return masks, pred_boxes, pred_class

    def _instance_segmentation_api(self, img_, object_name, threshold=0.5, rect_th=3):
        masks, boxes, pred_cls = self._get_prediction(img_, threshold)
        img = numpy.array(img_)
        img = cv2.cvtColor(img, cv2.COLOR_BGR2RGB)
        objects = []
        if object_name in pred_cls:
            main_object_idx = -1
            for i in range(len(masks)):
                if pred_cls[i] == object_name:
                    main_object_idx = i
                a1, a2, a3, a4 = (int(boxes[i][0][0])), (int(boxes[i][0][1])), \
                                 (int(boxes[i][1][0])), (int(boxes[i][1][1]))
                objects.append([pred_cls[i], img[a2:a4, a1:a3]])
            if len(objects) > 1:
                objects[0], objects[main_object_idx] = objects[main_object_idx], objects[0]
            return objects
        else:
            return None

    def fetch_from_video(self, video, object_name):
        cap = cv2.VideoCapture(video)
        while True:
            ret, frame = cap.read()
            objects = self._instance_segmentation_api(frame, object_name)
            if objects is not None:
                break
            if cv2.waitKey(1) & 0xFF == ord('q'):
                break
        cap.release()
        cv2.destroyAllWindows()
        for o in objects:
            cv2.imwrite('../output/' + o[0] + '.png', o[1])
        return objects
